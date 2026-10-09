#!/usr/bin/env python3
"""One entry point for every local check of this repository.

    python scripts/verify.py [--fetch-cache] [--skip-build]

In order: the pins (lean-toolchain and the Mathlib revision of lake-manifest.json are the committed
ones), the source guard, the definition comparison against OpenAI's challenge file, the statement
comparison between Challenge.lean and Solution.lean, the exact certificates under note/, the Lean
build of every target (including the Test audit, which fails on any axiom beyond propext,
Classical.choice and Quot.sound), the module-resolution check, the elaboration check of the compared
definitions (printed with pp.all from the Challenge and from SpernerCapacity.Defs, which must agree exactly,
as the registry's comparator demands), and Palomar's core-notation audit of the compared declarations. `--fetch-cache` runs `lake exe cache get` first (network); `--skip-build`
leaves out the four Lean steps. The last line is `VERIFY: PASS` or `VERIFY: FAIL`. Exit status 0 on
PASS only.
"""

from pathlib import Path
import json
import os
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
TOOLCHAIN = "leanprover/lean4:v4.35.0-rc2"
MATHLIB_REV = "065356127b1dc0016f66b7283ce0ce2c4055aa55"
TARGETS = ["SpernerCapacity", "Challenge", "Solution", "Test"]


def run(args, **kw):
    print("+", " ".join(args), flush=True)
    return subprocess.run(args, cwd=ROOT, text=True, encoding="utf-8", errors="replace", **kw)


def step(name, ok, detail=""):
    print(f"[{'ok' if ok else 'FAIL'}] {name}" + (f": {detail}" if detail else ""), flush=True)
    return ok


def check_pins():
    toolchain = (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip()
    manifest = json.loads((ROOT / "lake-manifest.json").read_text(encoding="utf-8"))
    revs = {p["name"]: p.get("rev") for p in manifest.get("packages", [])}
    ok = toolchain == TOOLCHAIN and revs.get("mathlib") == MATHLIB_REV
    return step("pins", ok, f"toolchain {toolchain}, mathlib {revs.get('mathlib')}")


def check_script(name, args):
    result = run([sys.executable] + args, capture_output=True)
    tail = (result.stdout + result.stderr).strip().splitlines()[-1:] or [""]
    return step(name, result.returncode == 0, tail[0])


def check_certificates():
    ok = True
    for path in sorted((ROOT / "note" / "certificates").glob("*/verify.py")):
        result = run([sys.executable, str(path)], capture_output=True)
        verdict = [line for line in result.stdout.splitlines() if line.startswith("VERDICT")]
        good = result.returncode == 0 and verdict == ["VERDICT: PASS"]
        ok &= step(f"certificate {path.parent.name}", good, verdict[-1] if verdict else "no verdict")
    return ok


def check_build():
    ok = True
    for target in TARGETS:
        result = run(["lake", "build", target], capture_output=True)
        bad = [line for line in result.stdout.splitlines() if "error" in line.lower()]
        ok &= step(f"lake build {target}", result.returncode == 0 and not bad,
                   bad[0] if bad else "built")
    return ok


def check_module_resolution():
    result = run(["lake", "env", sys.executable, "scripts/check_module_resolution.py"], capture_output=True)
    return step("module resolution", result.returncode == 0,
                (result.stdout + result.stderr).strip().splitlines()[-1:][0] if (result.stdout + result.stderr).strip() else "")


def check_definition_elaboration():
    """The compared definitions, printed with pp.all from the Challenge and from the development's
    definitions module, must agree exactly: the comparator judges the elaborated constants, which
    depend on the imports through instance resolution."""
    config = json.loads((ROOT / "comparator.json").read_text(encoding="utf-8"))
    names = config["definition_names"]
    scratch = ROOT / ".scratch"
    scratch.mkdir(exist_ok=True)
    outputs = []
    for module in (config["challenge_module"], "SpernerCapacity.Defs"):
        path = scratch / f"verify_pp_{module.replace('.', '_')}.lean"
        header = "import " + module + "\nset_option pp.all true\n"
        path.write_text(header + "".join("#print " + n + "\n" for n in names), encoding="utf-8")
        result = run(["lake", "env", "lean", str(path)], capture_output=True)
        outputs.append((result.returncode, result.stdout))
        path.unlink()
    ok = all(rc == 0 for rc, _ in outputs) and outputs[0][1].strip() != "" and outputs[0][1] == outputs[1][1]
    return step("definition elaboration (Challenge vs SpernerCapacity.Defs, pp.all)", ok,
                "identical" if ok else "the printed terms differ or a print failed")


def check_notation_audit():
    config = json.loads((ROOT / "comparator.json").read_text(encoding="utf-8"))
    args = ["lake", "env", "lean", "--run", "scripts/core_notation_audit.lean", config["challenge_module"]]
    for name in config["theorem_names"]:
        args += ["theorem", name]
    for name in config["definition_names"]:
        args += ["def", name]
    result = run(args, capture_output=True)
    try:
        rows = json.loads(result.stdout)
    except ValueError:
        rows = []
    expected = len(config["theorem_names"]) + len(config["definition_names"])
    names = {row.get("name") for row in rows} if isinstance(rows, list) else set()
    ok = result.returncode == 0 and len(names) == expected and \
        names == set(config["theorem_names"]) | set(config["definition_names"])
    return step("core-notation audit", ok, f"{len(names)} of {expected} declarations printed")


def main():
    fetch = "--fetch-cache" in sys.argv
    skip_build = "--skip-build" in sys.argv
    ok = check_pins()
    ok &= check_script("source guard", ["scripts/check-source.py"])
    ok &= check_script("definitions", ["scripts/check_definitions.py"])
    ok &= check_script("statements", ["scripts/check_statements.py"])
    ok &= check_certificates()
    if not skip_build:
        if fetch:
            ok &= step("lake exe cache get", run(["lake", "exe", "cache", "get"]).returncode == 0)
        ok &= check_build()
        ok &= check_module_resolution()
        ok &= check_definition_elaboration()
        ok &= check_notation_audit()
    print("VERIFY: PASS" if ok else "VERIFY: FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
