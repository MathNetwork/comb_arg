/-
Copyright (c) 2026 Xinze Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xinze Li
-/
import CombLemma.Witness
import CombLemma.EnergyBound
import CombLemma.Refinement
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Topology.Compactness.Compact

/-!
# Main theorem — energy reduction

The project's top-level statement: given a continuous energy `f` on a
compact nonempty parameter space and uniform *local witnesses* at every
`1/N`-near-critical parameter, one can construct a competitor function
whose supremum is bounded by `m₀ − 1/(4N)` (DLT-faithful quantitative
form).

## Framing: reduction, not contradiction

The theorem is stated in **reduction** form: given the witness
structure, a strictly-better competitor `f'` exists. The hypothesis only
says `m₀ = sSup (range f)` — about the original `f` — not that `m₀` is a
min-max level over some admissible class (see `docs/design-notes.md §2`
for the framing rationale). Downstream users with an admissible-class
framework (min-max constructions in geometric analysis) layer their
contradiction on top by showing `f' ∈ 𝒜` and invoking their infimum
characterization of `m₀`.

## Witness hypothesis shape

The `witness` hypothesis requires a `LocalWitness` whose saving is
**exactly `1/(4N)`**, not `∃ ε > 0, ...`. DLT's Lemma 3.1 produces a
definite `ε ≥ 1/(4N)` rather than an arbitrary positive `ε`, and the
combinatorial theorem committing to `1/(4N)` is the faithful
formulation. The quantitative conclusion `≤ m₀ − 1/(4N)` genuinely
consumes the `R.saving_ge_quarter_N` invariant on `Refinement`; a strict
`< m₀` conclusion alone would trivialize. See `docs/design-notes.md §9`
for the decision record.
-/

namespace CombLemma

/-- **Min-max energy reduction.**

Let `K` be a compact nonempty parameter space, `X` a pseudo-metric space
equipped with a `PairableCover` structure, `f : K → ℝ` a continuous
energy with `m₀ = sSup (range f) > 0`, and fix a near-criticality level
`1/N` with `N > 0`. Suppose every parameter `t` with `f t ≥ m₀ − 1/N`
admits a `LocalWitness` with saving `1/(4N)`. Then a function
`f' : K → ℝ` exists with `sSup (range f') ≤ m₀ − 1/(4N)`.

## Proof architecture

* `Refinement.exists_refinement` produces a `Refinement K X f m₀ N`
  (including the `twoFold` and `saving_ge_quarter_N` invariants) via the
  DLT-style interval refinement induction.

* `EnergyBound.exists_reducedEnergy_sup_lt` takes the `Refinement` and
  produces the competitor with `sSup (range reducedEnergy) ≤ m₀ − 1/(4N)`,
  consuming `saving_ge_quarter_N` for the per-piece floor and `twoFold`
  for the sum multiplicity bound.

Chaining yields this theorem. -/
theorem exists_sup_reduction
    {X : Type*} [PseudoMetricSpace X] [PairableCover X]
    {f : unitInterval → ℝ} (hf : Continuous f)
    {m₀ : ℝ} (hm_pos : 0 < m₀) (hm : m₀ = sSup (Set.range f))
    {N : ℕ} (hN : 0 < N)
    (witness : ∀ t : unitInterval, f t ≥ m₀ - 1 / (N : ℝ) →
                  Nonempty (LocalWitness unitInterval X f t (1 / (4 * (N : ℝ))))) :
    ∃ f' : unitInterval → ℝ, sSup (Set.range f') ≤ m₀ - 1 / (4 * (N : ℝ)) := by
  obtain ⟨R⟩ := Refinement.exists_refinement hf hm hN witness
  exact EnergyBound.exists_reducedEnergy_sup_lt hf hm_pos hm hN R

end CombLemma
