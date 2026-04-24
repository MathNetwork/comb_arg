/-
Copyright (c) 2026 Xinze Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xinze Li
-/
import CombArg.Core
import CombArg.Refinement
import CombArg.Witness
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Topology.Compactness.Compact

/-!
# Application — 1D sup reduction

The 1D application of the abstract core theorem
`CombArg.exists_sup_reduction_of_cover` (in `CombArg/Core.lean`).

Given a continuous energy `f : unitInterval → ℝ` with `m₀ = sSup
(range f)`, `N > 0`, and pointwise `LocalWitness`es with saving
`1/(4N)` at every `1/N`-near-critical parameter, a competitor
`f' : unitInterval → ℝ` exists with
`sSup (range f') ≤ m₀ − 1/(4N)` — the DLT-faithful quantitative form.

## Architecture

The theorem is the composition of two steps:

1. **1D cover construction** — `Refinement.exists_refinement` consumes
   the `LocalWitness` hypothesis and produces a
   `FiniteCoverWithWitnesses unitInterval f m₀ (1/N) (1/(4N))` via
   the DLT §3.2 Step 1 interval-refinement induction.

2. **Abstract core** — `exists_sup_reduction_of_cover` takes the
   cover and produces the sup-reducing competitor by scalar
   arithmetic.

Future applications (e.g. `K = [0,1]^m`) add a second cover-construction
path into the same core; step 2 is unchanged.

## Framing: reduction, not contradiction

The theorem is stated in **reduction** form: given the witness
structure, a strictly-better competitor `f'` exists. The hypothesis
only says `m₀ = sSup (range f)` — about the original `f` — not that
`m₀` is a min-max level over some admissible class (see
`docs/design-notes.md §2`). Downstream users with an admissible-class
framework (min-max constructions in geometric analysis) layer their
contradiction on top.
-/

namespace CombArg

/-- **1D sup reduction** — application of the abstract core theorem
`exists_sup_reduction_of_cover` to `K = unitInterval` with
`δ = 1/N`, `ε = 1/(4N)`.

Let `f : unitInterval → ℝ` be continuous with `m₀ = sSup (range f)`,
`m₀ > 0`, and fix `N > 0`. Suppose every parameter `t` with
`f t ≥ m₀ − 1/N` admits a `LocalWitness` with saving `1/(4N)`. Then
a competitor `f' : unitInterval → ℝ` exists with
`sSup (range f') ≤ m₀ − 1/(4N)`.

## Proof architecture

`Refinement.exists_refinement` produces a
`FiniteCoverWithWitnesses unitInterval f m₀ (1/N) (1/(4N))` via the
DLT-style interval refinement induction; `exists_sup_reduction_of_cover`
then converts the cover into the sup-reducing competitor by scalar
arithmetic. -/
theorem exists_sup_reduction
    {X : Type*} [PseudoMetricSpace X] [PairableCover X]
    {f : unitInterval → ℝ} (hf : Continuous f)
    {m₀ : ℝ} (_hm_pos : 0 < m₀) (hm : m₀ = sSup (Set.range f))
    {N : ℕ} (hN : 0 < N)
    (witness : ∀ t : unitInterval, f t ≥ m₀ - 1 / (N : ℝ) →
                  Nonempty (LocalWitness unitInterval X f t (1 / (4 * (N : ℝ))))) :
    ∃ f' : unitInterval → ℝ, sSup (Set.range f') ≤ m₀ - 1 / (4 * (N : ℝ)) := by
  obtain ⟨C⟩ := Refinement.exists_refinement hf hm hN witness
  have hN_real : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN
  have hδ : (0 : ℝ) < 1 / (N : ℝ) := one_div_pos.mpr hN_real
  have hε : (0 : ℝ) < 1 / (4 * (N : ℝ)) := by positivity
  have hle : 1 / (4 * (N : ℝ)) ≤ 1 / (N : ℝ) := by
    apply one_div_le_one_div_of_le hN_real
    linarith
  exact exists_sup_reduction_of_cover hf hm hδ hε hle C

end CombArg
