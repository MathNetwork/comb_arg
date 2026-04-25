/-
Copyright (c) 2026 Xinze Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xinze Li
-/
import CombArg

/-!
# Minimal worked example: `CombArg.exists_sup_reduction`

End-to-end invocation of the one-parameter sup-reduction
corollary on the simplest possible input — a constant energy
`f ≡ 1 : unitInterval → ℝ`, parameterized by an arbitrary
near-criticality parameter `N : ℕ` with `0 < N`. The example
is mathematically trivial (the supremum of a constant is the
constant) but exercises every component of the public API:
`LocalWitness`, the witness hypothesis, and the output
existential.

## Reading guide

A consumer of `CombArg.exists_sup_reduction` supplies:

* a continuous `f : unitInterval → ℝ`;
* a level `m₀ : ℝ` with `m₀ = sSup (Set.range f)`;
* a near-criticality parameter `N : ℕ` with `0 < N`;
* for every `t : unitInterval` with `f t ≥ m₀ − 1/N`, a
  `LocalWitness unitInterval f t (1/(4·N))`: an open
  neighborhood of `t`, a continuous replacement-energy
  function on `unitInterval`, and the saving bound
  `f s − replacementEnergy s ≥ 1/(4·N)` on the neighborhood.

The output is a competitor `f' : unitInterval → ℝ` with a
modification set `S` containing the `1/N`-near-critical set,
satisfying pointwise dominance `f' ≤ f`, off-`S` agreement
`f' = f`, and the sup bound `sSup (range f') ≤ m₀ − 1/(4·N)`.

In a GMT instantiation, the witness comes from De
Lellis–Tasnady (2013) Lemma 3.1 (existence of a replacement
family), Pitts (1981)'s analogue, or equivalent. Constructing
that witness is the substantive non-combinatorial work; this
library treats it as input.
-/

namespace CombArg.Example

open scoped Classical

/-- The constant function `f ≡ 1 : unitInterval → ℝ`. -/
noncomputable def constOne : unitInterval → ℝ := fun _ => 1

/-- For the constant energy `f ≡ 1` on the unit interval and any
`N : ℕ`, the global replacement `s ↦ 1 − 1/(4·N)` realizes a
`LocalWitness` at every `t` with neighborhood `Set.univ` and
saving exactly `1/(4·N)`. -/
noncomputable def constOneWitness (N : ℕ) (t : unitInterval) :
    LocalWitness unitInterval constOne t (1 / (4 * (N : ℝ))) where
  neighborhood := Set.univ
  isOpen_neighborhood := isOpen_univ
  t_mem := Set.mem_univ _
  replacementEnergy := fun _ => 1 - 1 / (4 * (N : ℝ))
  replacementEnergy_continuous := continuous_const
  saving_bound := fun _ _ => by
    show constOne _ - (1 - 1 / (4 * (N : ℝ))) ≥ 1 / (4 * (N : ℝ))
    show (1 : ℝ) - (1 - 1 / (4 * (N : ℝ))) ≥ 1 / (4 * (N : ℝ))
    linarith

/-- `exists_sup_reduction` invoked on `constOne` for arbitrary
`N > 0`: a competitor `f'` exists undercutting the constant level
`1` by at least `1/(4·N)` on the whole unit interval. -/
example (N : ℕ) (hN : 0 < N) :
    ∃ (f' : unitInterval → ℝ) (S : Set unitInterval),
      {t : unitInterval | constOne t ≥ 1 - 1 / (N : ℝ)} ⊆ S ∧
      (∀ t, f' t ≤ constOne t) ∧
      (∀ t, t ∉ S → f' t = constOne t) ∧
      sSup (Set.range f') ≤ 1 - 1 / (4 * (N : ℝ)) :=
  CombArg.exists_sup_reduction (f := constOne) (m₀ := 1) (N := N)
    continuous_const
    (by rw [show Set.range constOne = {1} from Set.range_const];
        exact (csSup_singleton _).symm)
    hN
    (fun t _ => constOneWitness N t)

end CombArg.Example
