/-
Copyright (c) 2026 Xinze Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xinze Li
-/
import CombArg
import Lean

/-!
# `lake exe combarg-audit`

One-command health check for the `CombArg` library.  Performs:

1. **Axiom audit.**  Reads the imported `CombArg` environment and
   transitively walks the proof terms of the five public theorems
   (`exists_sup_reduction`, `exists_sup_reduction_of_cover`,
   `OneDim.exists_refinement`, `OneDim.exists_DLTCover`,
   `Scalar.exists_refinement_partition`).  Confirms that the only
   foundational axioms reached are `propext`, `Classical.choice`,
   and `Quot.sound`.  Any other axiom (e.g. `sorryAx`) causes a
   nonzero exit.

2. **Public-API listing.**  Prints the public declarations of the
   library and their kinds (`structure` vs `theorem`).

3. **Structure-field stability.**  Walks the field list of each
   public structure and compares against a hard-coded baseline.
   Silent additions or removals of public fields cause the audit to
   fail, ensuring `README`'s stable-API contract is mechanically
   enforced rather than honor-system.

The exit code is `0` on success and `1` on any audit failure.
Intended for both interactive use (developer one-shot check) and
CI invocation.
-/

open Lean

/-- Set of foundational axioms expected for every public theorem. -/
private def expectedAxioms : NameSet :=
  NameSet.empty
    |>.insert ``propext
    |>.insert ``Classical.choice
    |>.insert ``Quot.sound

/-- Walk the environment from `name`, accumulating every constant of
kind `axiomInfo` reachable through `value?` references. -/
private partial def collectAxiomDeps (env : Environment)
    (name : Name) (visited : NameSet := {}) (acc : NameSet := {}) :
    NameSet × NameSet :=
  if visited.contains name then
    (visited, acc)
  else
    let visited := visited.insert name
    match env.find? name with
    | none => (visited, acc)
    | some (.axiomInfo _) => (visited, acc.insert name)
    | some info =>
      let body := info.value?.getD (.const name [])
      body.foldConsts (init := (visited, acc))
        fun n (v, a) => collectAxiomDeps env n v a

/-- Audit one named theorem. Returns `true` on success. -/
private def auditTheorem (env : Environment) (thm : Name) : IO Bool := do
  let (_, axs) := collectAxiomDeps env thm
  let unexpected := axs.toList.filter (fun a => !expectedAxioms.contains a)
  if unexpected.isEmpty then
    IO.println s!"  ✓ {thm}"
    return true
  else
    IO.println s!"  ✗ {thm} — unexpected axioms: {unexpected}"
    return false

/-! ## Structure-field stability -/

/-- Expected fields of each public structure, as stated in the
README's stable-API list. The audit compares the env-reported field
set to this baseline; any drift (silent addition or removal) is a
failure. -/
private def expectedStructureFields : List (Name × List Name) :=
  [ (``CombArg.LocalWitness,
      [`neighborhood, `isOpen_neighborhood, `t_mem,
       `replacementEnergy, `replacementEnergy_continuous,
       `saving_bound])
  , (``CombArg.FiniteCoverWithWitnesses,
      [`ι, `ιFintype, `nonempty, `piece,
       `covers_delta_near_critical, `replacementEnergy, `saving,
       `saving_pos, `saving_bound, `twoFold, `saving_ge_eps])
  , (``CombArg.OneDim.DLTCover,
      [`initialCover, `L, `L_pos, `refinement, `σ_injective,
       `initialCover_covered])
  , (``CombArg.OneDim.SkippedSpacedIntervals,
      [`n, `intervalCenter, `radius, `radius_pos,
       `two_fold_spacing])
  , (``CombArg.OneDim.InitialCover,
      [`toSkippedSpacedIntervals, `n_pos, `witnessCenter,
       `witnessCenter_mem_nearCritical, `wit,
       `I_subset_neighborhood, `covers])
  , (``CombArg.OneDim.PartialRefinement,
      [`J, `σ, `J_subset, `processed_cover]) ]

/-- Audit a single structure: confirm its env-reported field list
matches the declared baseline. -/
private def auditStructure (env : Environment)
    (sname : Name) (expected : List Name) : IO Bool := do
  let actual := getStructureFields env sname
  let actualList := actual.toList
  let expectedSet : NameSet := expected.foldl (·.insert ·) {}
  let actualSet : NameSet := actual.foldl (·.insert ·) {}
  let missing := expected.filter (fun n => !actualSet.contains n)
  let extra := actualList.filter (fun n => !expectedSet.contains n)
  if missing.isEmpty && extra.isEmpty then
    IO.println s!"  ✓ {sname} ({actualList.length} fields)"
    return true
  else
    IO.println s!"  ✗ {sname} — field set drifted from baseline"
    if !missing.isEmpty then
      IO.println s!"    missing: {missing}"
    if !extra.isEmpty then
      IO.println s!"    extra:   {extra}"
    return false

/-- Public declarations: their names and what to call them. -/
private def publicDecls : List (Name × String) :=
  [ (``CombArg.LocalWitness, "structure  (input)")
  , (``CombArg.FiniteCoverWithWitnesses, "structure  (input/output)")
  , (``CombArg.OneDim.DLTCover,
       "structure  (DLT-style structured output)")
  , (``CombArg.OneDim.exists_DLTCover,
       "theorem    (DLT construction, structured form)")
  , (``CombArg.OneDim.exists_refinement,
       "theorem    (combinatorial main: 1D witnesses → cover, DLT path)")
  , (``CombArg.Scalar.exists_refinement_partition,
       "theorem    (alternative scalar proof: partition by endpoints)")
  , (``CombArg.exists_sup_reduction_of_cover,
       "theorem    (bookkeeping corollary, generic K)")
  , (``CombArg.exists_sup_reduction,
       "theorem    (chained 1D corollary)") ]

def main : IO UInt32 := do
  Lean.initSearchPath (← Lean.findSysroot)
  let env ← Lean.importModules #[(`CombArg : Import)] {} (trustLevel := 0)

  IO.println "CombArg library audit"
  IO.println (String.replicate 21 '=')
  IO.println ""

  IO.println "Public declarations:"
  for (n, kind) in publicDecls do
    if env.contains n then
      IO.println s!"  • {n}\n      {kind}"
    else
      IO.println s!"  ✗ {n} — NOT FOUND in environment"
      return 1
  IO.println ""

  IO.println "Foundational-axiom audit:"
  let theorems :=
    [ ``CombArg.exists_sup_reduction
    , ``CombArg.exists_sup_reduction_of_cover
    , ``CombArg.OneDim.exists_refinement
    , ``CombArg.OneDim.exists_DLTCover
    , ``CombArg.Scalar.exists_refinement_partition ]
  let mut allOk := true
  for thm in theorems do
    let ok ← auditTheorem env thm
    if !ok then allOk := false
  IO.println ""

  IO.println "Structure-field stability:"
  for (sname, expected) in expectedStructureFields do
    let ok ← auditStructure env sname expected
    if !ok then allOk := false
  IO.println ""

  if allOk then
    IO.println "All public theorems depend only on:"
    IO.println "  propext, Classical.choice, Quot.sound"
    IO.println ""
    IO.println "All public structures match their declared field"
    IO.println "baselines (see Audit.lean expectedStructureFields)."
    IO.println ""
    IO.println "Library status: ✓ healthy"
    return 0
  else
    IO.println "Library status: ✗ audit FAILED"
    return 1
