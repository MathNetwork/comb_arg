/-
Copyright (c) 2026 Xinze Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xinze Li
-/
import CombArg

/-!
# Smoke tests

Three guards on the public API:

1. **`LocalWitness` constructibility** — a non-trivial witness on
   the constant function `f ≡ 1` is built explicitly.
2. **`exists_sup_reduction` end-to-end elaboration** — the public
   theorem is invoked in full on `f ≡ 1` with an arbitrary
   `N : ℕ`, confirming that every component of the witness
   hypothesis can be discharged.
3. **Axiom audit** — `#print axioms` on each public theorem
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

/-! ## (3) Axiom audit

The three messages below should each read exactly

    depends on axioms: [propext, Classical.choice, Quot.sound]

CI logs surface this; regression on extra axioms shows up here. -/

#print axioms CombArg.exists_sup_reduction
#print axioms CombArg.exists_sup_reduction_of_cover
#print axioms CombArg.Refinement.exists_refinement

end CombArg.Test
