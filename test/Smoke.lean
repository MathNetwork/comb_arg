/-
Copyright (c) 2026 Xinze Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xinze Li
-/
import CombArg

/-!
# Smoke tests

Five guards on the public API:

1. **`LocalWitness` constructibility** — a non-trivial witness on
   the constant function `f ≡ 1` is built explicitly.
2. **`exists_sup_reduction` end-to-end elaboration** — the public
   theorem is invoked in full on `f ≡ 1` with an arbitrary
   `N : ℕ`, confirming that every component of the witness
   hypothesis can be discharged.
3. **Abstract-`K` `exists_sup_reduction_of_cover` invocation** —
   the K-generic bookkeeping corollary is invoked on
   `K = Fin 2` (a non-`unitInterval` parameter space), confirming
   that the bookkeeping path does not silently depend on
   1D specifics.
4. **`Scalar.exists_refinement_partition` end-to-end elaboration**
   — the alternative cheap proof of the abstract scalar theorem is
   invoked on the same `f ≡ 1` setup, confirming the partition
   route accepts the same witness hypothesis as
   `OneDim.exists_refinement`.
5. **Axiom audit** — `#print axioms` on each public theorem
   confirms dependence on exactly the three standard Lean 4 /
   Mathlib foundational axioms (`propext`, `Classical.choice`,
   `Quot.sound`). A regression that introduces a new axiom
   surfaces here.
-/

namespace CombArg.Test

open scoped Classical

/-! ## (1) `LocalWitness` constructibility

For the constant `f ≡ 1` and any `N : ℕ`, the replacement
`s ↦ 1 − 1/(4·N)` realizes a `LocalWitness` at every `t` with
neighborhood `Set.univ` and saving exactly `1/(4·N)`. -/

private noncomputable def constOneWitness (N : ℕ) (t : unitInterval) :
    LocalWitness unitInterval (fun _ => (1 : ℝ)) t (1 / (4 * (N : ℝ))) where
  neighborhood := Set.univ
  isOpen_neighborhood := isOpen_univ
  t_mem := Set.mem_univ _
  replacementEnergy := fun _ => 1 - 1 / (4 * (N : ℝ))
  replacementEnergy_continuous := continuous_const
  saving_bound := fun _ _ => by
    show (1 : ℝ) - (1 - 1 / (4 * (N : ℝ))) ≥ 1 / (4 * (N : ℝ))
    linarith

/-! ## (2) End-to-end invocation

Apply `exists_sup_reduction` to the constant function for an
arbitrary `N > 0`; existence of `f'` and `S` follows immediately
from the bundled witness. -/

example (N : ℕ) (hN : 0 < N) :
    ∃ (f' : unitInterval → ℝ) (S : Set unitInterval),
      {t : unitInterval | (fun _ : unitInterval => (1 : ℝ)) t ≥ 1 - 1 / (N : ℝ)} ⊆ S ∧
      (∀ t, f' t ≤ (fun _ : unitInterval => (1 : ℝ)) t) ∧
      (∀ t, t ∉ S → f' t = (fun _ : unitInterval => (1 : ℝ)) t) ∧
      sSup (Set.range f') ≤ 1 - 1 / (4 * (N : ℝ)) :=
  CombArg.exists_sup_reduction (f := fun _ => (1 : ℝ)) (m₀ := 1) (N := N)
    continuous_const
    (by rw [Set.range_const]; exact (csSup_singleton _).symm)
    hN
    (fun t _ => constOneWitness N t)

/-! ## (3) Abstract-`K` invocation of the bookkeeping corollary

A minimal `FiniteCoverWithWitnesses` on `K = Fin 2`: the constant
energy `f ≡ 1`, single piece equal to `Set.univ`, replacement
`≡ 1/2`, saving `1/2`. Confirms `exists_sup_reduction_of_cover`
elaborates against a parameter space that is not `unitInterval`. -/

example :
    ∃ f' : Fin 2 → ℝ,
      (∀ t, f' t ≤ (fun _ : Fin 2 => (1 : ℝ)) t) ∧
      sSup (Set.range f') ≤ 1 - (1 / 2 : ℝ) := by
  have C : FiniteCoverWithWitnesses (Fin 2) (fun _ => (1 : ℝ)) 1 1 (1 / 2) :=
    { ι := Unit
      ιFintype := inferInstance
      nonempty := ⟨()⟩
      piece := fun _ => Set.univ
      covers_delta_near_critical := fun _ _ => Set.mem_iUnion.mpr ⟨(), trivial⟩
      replacementEnergy := fun _ _ => (1 / 2 : ℝ)
      saving := fun _ => (1 / 2 : ℝ)
      saving_pos := fun _ => by norm_num
      saving_bound := fun _ _ _ => by show (1 : ℝ) - 1 / 2 ≥ 1 / 2; norm_num
      twoFold := fun _ => by
        -- Unit-indexed pieces all equal univ; filter is univ;
        -- |univ : Finset Unit| = 1 ≤ 2.
        simp
      saving_ge_eps := fun _ => le_refl _ }
  obtain ⟨f', h_le, _, h_sup⟩ :=
    CombArg.exists_sup_reduction_of_cover (f := fun _ => (1 : ℝ))
      (K := Fin 2) continuous_const
      (by rw [Set.range_const]; exact (csSup_singleton _).symm)
      (by norm_num : (1 / 2 : ℝ) ≤ 1) C
  exact ⟨f', h_le, h_sup⟩

/-! ## (4) Partition-route invocation

Apply `Scalar.exists_refinement_partition` to the same constant
function used in (2). Confirms the alternative cheap proof of the
abstract scalar theorem accepts the same `LocalWitness` hypothesis
as `OneDim.exists_refinement` and produces the same abstract output
type. -/

example (N : ℕ) (hN : 0 < N) :
    Nonempty (FiniteCoverWithWitnesses unitInterval (fun _ => (1 : ℝ)) 1
              (1 / (N : ℝ)) (1 / (4 * (N : ℝ)))) :=
  CombArg.Scalar.exists_refinement_partition
    (f := fun _ => (1 : ℝ)) (m₀ := 1) (N := N)
    continuous_const
    (by rw [Set.range_const]; exact (csSup_singleton _).symm)
    hN
    (fun t _ => constOneWitness N t)

/-! ## (5) Axiom audit (regression guard)

`#guard_msgs in #print axioms` asserts the exact set of foundational
axioms each public theorem depends on. If a regression introduces a
new axiom (an accidental `sorry`'s `sorryAx`, a custom `axiom`
declaration, a heavier Mathlib import bringing in additional
foundational axioms), the build **fails** with the new axiom list as
a diagnostic. -/

/-- info: 'CombArg.exists_sup_reduction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CombArg.exists_sup_reduction

/-- info: 'CombArg.exists_sup_reduction_of_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CombArg.exists_sup_reduction_of_cover

/-- info: 'CombArg.OneDim.exists_refinement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CombArg.OneDim.exists_refinement

/-- info: 'CombArg.OneDim.exists_DLTCover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CombArg.OneDim.exists_DLTCover

/-- info: 'CombArg.Scalar.exists_refinement_partition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CombArg.Scalar.exists_refinement_partition

end CombArg.Test
