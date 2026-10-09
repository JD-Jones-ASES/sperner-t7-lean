module

import Solution
import Lean.Util.CollectAxioms

/-!
# Axiom audit

A module file importing `Solution` (not `Challenge.lean`). Walks every constant of the environment
whose name begins with `SpernerCapacity.`, `_private.SpernerCapacity.` or `_private.Solution.` (the
public declarations of this development; the private auxiliaries that Lean generates are not
enumerated under the module system, but `collectAxioms` reaches every private constant a public proof
refers to, including a private `axiom`), and collects the axioms each depends on. Anything outside
`propext`, `Classical.choice`, `Quot.sound` is reported with `logError`, which fails `lake build`.
The audit also fails if it matched fewer constants than the floor below (so a renamed namespace
cannot make it pass vacuously) or if any of the nineteen compared theorems is missing from the
environment.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut checked : Nat := 0
  let mut rejected : Nat := 0
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for (name, _) in env.constants.toList do
    let label := name.toString
    if label.startsWith "SpernerCapacity." || label.startsWith "_private.SpernerCapacity." ||
        label.startsWith "_private.Solution." then
      checked := checked + 1
      let axs ← collectAxioms name
      for ax in axs do
        unless allowed.contains ax do
          rejected := rejected + 1
          logError m!"Unexpected axiom dependency: {name} -> {ax}"
  unless checked ≥ 200 do
    logError m!"Axiom audit matched only {checked} project constants; expected at least 200"
  for n in [`SpernerCapacity.T7_isTournament,
      `SpernerCapacity.transitiveNumber_T7,
      `SpernerCapacity.T7_square_witness,
      `SpernerCapacity.T7_exists_clique_gt_four_pow,
      `SpernerCapacity.four_lt_capacity_T7,
      `SpernerCapacity.sqrt18_le_capacity_T7,
      `SpernerCapacity.capacity_T7_le_five,
      `SpernerCapacity.transitiveNumber_lt_capacity_T7,
      `SpernerCapacity.lift_lemma,
      `SpernerCapacity.rpow_le_capacity,
      `SpernerCapacity.transitiveNumber_le_capacity,
      `SpernerCapacity.capacity_le_of_factorization,
      `SpernerCapacity.capacity_le_card,
      `SpernerCapacity.paley_isTournament,
      `SpernerCapacity.transitiveNumber_paley,
      `SpernerCapacity.five_lt_capacity_paley,
      `SpernerCapacity.sqrt29_le_capacity_paley,
      `SpernerCapacity.capacity_eq_transitiveNumber_of_card_le_six,
      `SpernerCapacity.seven_le_card_of_transitiveNumber_lt_capacity] do
    unless env.contains n do
      logError m!"Compared theorem is missing from the environment: {n}"
  logInfo m!"Audited {checked} project constants; unexpected axiom dependencies: {rejected}."
