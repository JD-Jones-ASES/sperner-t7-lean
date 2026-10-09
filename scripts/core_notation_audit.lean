module
-- Palomar's core-notation audit, an unmodified copy of scripts/core_notation_audit.lean of
-- https://github.com/PalomarRegistry/PalomarSubmission (main, fetched 2026-10-07 UTC); see that
-- repository for its licence. Used only to check the statement surface locally.

import Lean
import Lean.Util.FoldConsts

open Lean

private structure AuditRow where
  name : String
  declaration : String
deriving ToJson

private def usage : String :=
  "usage: palomar-audit MODULE (theorem|def NAME)+"

private def plainName (text : String) : IO Name := do
  if text.isEmpty then
    throw <| IO.userError usage
  let name := text.toName
  unless name.toString (escape := false) == text do
    throw <| IO.userError s!"audit name is not an unambiguous dotted Lean name: {text}"
  return name

private def parseRequests (args : List String) : IO (Name × Array (String × String × Name)) := do
  let moduleText :: requestArgs := args
    | throw <| IO.userError usage
  if requestArgs.isEmpty then
    throw <| IO.userError usage
  let rec loop (remaining : List String) (requests : Array (String × String × Name)) := do
    match remaining with
    | [] => pure requests
    | kind :: name :: tail =>
      unless kind == "theorem" || kind == "def" do
        throw <| IO.userError usage
      loop tail (requests.push (kind, name, ← plainName name))
    | _ => throw <| IO.userError usage
  return (← plainName moduleText, ← loop requestArgs #[])

private def validateRequest
    (rawEnv coreEnv : Environment) (moduleName : Name)
    (request : String × String × Name) : IO Unit := do
  let (kind, nameText, name) := request
  let some info := rawEnv.find? name
    | throw <| IO.userError s!"audit declaration is missing: {nameText}"
  let some moduleIdx := rawEnv.getModuleIdxFor? name
    | throw <| IO.userError s!"audit declaration has no imported module: {nameText}"
  unless rawEnv.header.moduleNames[moduleIdx]? == some moduleName do
    throw <| IO.userError s!"audit declaration is not defined by {moduleName}: {nameText}"
  if coreEnv.contains name then
    throw <| IO.userError s!"audit declaration collides with a trusted Lean constant: {nameText}"
  match kind, info with
  | "theorem", .thmInfo _ => pure ()
  | "def", .defnInfo _ => pure ()
  | _, _ =>
    throw <| IO.userError s!"audit declaration kind does not match comparator config: {nameText}"

/--
Copy only declaration names, universe parameters, and types into the trusted
pretty-printing environment. No submitted environment-extension state crosses
this boundary. Each proxy is rechecked as an axiom before it is used to let
Lean inspect types while printing another type.
-/
private partial def addTypeProxy
    (rawEnv : Environment) (name : Name) : StateT (Environment × NameSet) IO Unit := do
  let (env, seen) ← get
  if env.contains name || seen.contains name then
    return
  let some dependency := rawEnv.find? name
    | throw <| IO.userError s!"audit declaration depends on missing constant {name}"
  set (env, seen.insert name)
  for used in dependency.type.getUsedConstants do
    addTypeProxy rawEnv used
  let (env, seen) ← get
  let proxy : Declaration := .axiomDecl {
    name := dependency.name
    levelParams := dependency.levelParams
    type := dependency.type
    isUnsafe := false
  }
  -- The proxies exist only so the trusted printer can resolve the constants a
  -- type mentions. Their types were already kernel-checked in the submitted
  -- module and again by the mechanical stage. Rechecking them here, in an
  -- environment that holds every Mathlib definition as an opaque axiom, fails
  -- whenever a type needs an abbreviation (`FunLike`, `SmallCategory`) or an
  -- instance diamond unfolded, so the kernel is skipped for the copy.
  let ctx : Core.Context := {
    fileName := "<palomar-core-notation-audit-proxy>"
    fileMap := default
    options := ({} : Options).setBool `debug.skipKernelTC true
  }
  let (_, state) ← (Lean.addDecl proxy).toIO ctx { env }
  set (state.env, seen)

private def addTypeProxies
    (rawEnv : Environment) (trustedEnv : Environment) (roots : Array Name) : IO Environment := do
  let (_, env, _) ← StateT.run (roots.forM (addTypeProxy rawEnv)) (trustedEnv, {})
  return env

private def printSignature (env : Environment) (name : Name) : IO String := do
  unless env.contains name do
    throw <| IO.userError s!"audit declaration is missing: {name}"
  let opts := ({} : Options)
    |>.set `pp.notation false
    |>.set `pp.fullNames true
    |>.set `pp.fieldNotation false
    |>.set `pp.proofs true
    |>.set `pp.deepTerms true
    |>.set `pp.maxSteps 1000000
  let ctx : Core.Context := {
    fileName := "<palomar-core-notation-audit>"
    fileMap := default
    options := opts
  }
  let state : Core.State := { env }
  let (signature, _) ← (PrettyPrinter.ppSignature name).run' {} |>.toIO ctx state
  return signature.fmt.pretty

public unsafe def main (args : List String) : IO UInt32 := do
  let sysroot ← findSysroot
  initSearchPath sysroot
  let (moduleName, requests) ← parseRequests args

  -- `loadExts := false` is the security boundary: imported delaborators,
  -- unexpanders, formatters, and other author-controlled extensions remain
  -- serialized data and are never initialized or evaluated.
  let rawEnv ← importModules (loadExts := false) #[{ module := moduleName }] {} 0

  -- Do not resolve the trusted pretty-printer through candidate LEAN_PATH.
  -- The raw import deliberately initializes no environment extensions,
  -- including Lean's; only the toolchain library is allowed to initialize in
  -- the separate environment used to print the copied types.
  searchPathRef.set [← getLibDir sysroot]
  enableInitializersExecution
  let coreEnv ← importModules (loadExts := true) #[{ module := `Lean }] {} 0
  requests.forM (validateRequest rawEnv coreEnv moduleName)
  let env ← addTypeProxies rawEnv coreEnv (requests.map (fun request => request.2.2))

  let mut rows : Array AuditRow := #[]
  let mut totalBytes := 0
  for (kind, nameText, name) in requests do
    let declaration := s!"{kind} {← printSignature env name}"
    totalBytes := totalBytes + declaration.utf8ByteSize
    if totalBytes > 512 * 1024 then
      throw <| IO.userError "audit declarations exceed the 512 KiB limit"
    rows := rows.push { name := nameText, declaration }
  IO.println (toJson rows).compress
  return 0
