/-
Copyright (c) 2026 Xinze Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xinze Li
-/
import CombArg.Cover
import CombArg.OneDim
import CombArg.Witness
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Topology.Compactness.Compact

/-!
# One-parameter sup-reduction corollary

The 1D composition of the combinatorial main theorem
`CombArg.OneDim.exists_refinement` with the sup-reduction
bookkeeping corollary
`CombArg.exists_sup_reduction_of_cover` (in `CombArg/Core.lean`).

Given a continuous energy `f : unitInterval → ℝ` with `m₀ = sSup
(range f)`, `N > 0`, and pointwise `LocalWitness`es with saving
`1/(4N)` at every `1/N`-near-critical parameter, a competitor
`f' : unitInterval → ℝ` exists with
`sSup (range f') ≤ m₀ − 1/(4N)` — the DLT-faithful quantitative form.

## Architecture

The theorem is the composition of two steps:

1. **Combinatorial main theorem** — `OneDim.exists_refinement`
   consumes the `LocalWitness` hypothesis and produces a
   `FiniteCoverWithWitnesses unitInterval f m₀ (1/N) (1/(4N))` via
   the DLT §3.2 Step 1 interval-refinement induction.

2. **Bookkeeping corollary** — `exists_sup_reduction_of_cover`
   takes the cover and produces the sup-reducing competitor by
   scalar arithmetic.

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

/-- **One-parameter sup-reduction corollary** — composition of
the combinatorial main theorem `OneDim.exists_refinement`
with the bookkeeping corollary `exists_sup_reduction_of_cover`
on `K = unitInterval` with `δ = 1/N`, `ε = 1/(4N)`.

Let `f : unitInterval → ℝ` be continuous with `m₀ = sSup (range f)`,
`m₀ > 0`, and fix `N > 0`. Suppose every parameter `t` with
`f t ≥ m₀ − 1/N` admits a `LocalWitness` with saving `1/(4N)`.
Then a competitor `f' : unitInterval → ℝ` together with a
modification set `S ⊆ unitInterval` exist with

* **coverage** — `S` contains the `1/N`-near-critical set;
* **(a)** pointwise dominance — `f' t ≤ f t` for every `t`;
* **(b)** localization — `f' t = f t` whenever `t ∉ S`;
* **(c)** supremum bound — `sSup (range f') ≤ m₀ − 1/(4N)`.

(a)(b) anchor `f'` to `f`: without them, any constant
`f' ≡ c ≤ m₀ − 1/(4N)` would satisfy (c) vacuously. (b) forces
`f' = f` everywhere outside `S`, so generic non-constant `f`
forbids constant competitors.

## Proof architecture

`OneDim.exists_refinement` produces a
`FiniteCoverWithWitnesses unitInterval f m₀ (1/N) (1/(4N))` via
the DLT-style interval refinement induction;
`exists_sup_reduction_of_cover` then converts the cover into the
sup-reducing competitor by scalar arithmetic. The modification
set `S` is exposed as `⋃ l, C.piece l`. -/
theorem exists_sup_reduction
    {f : unitInterval → ℝ} (hf : Continuous f)
    {m₀ : ℝ} (hm : m₀ = sSup (Set.range f))
    {N : ℕ} (hN : 0 < N)
    (witness : ∀ t : unitInterval, f t ≥ m₀ - 1 / (N : ℝ) →
                  LocalWitness unitInterval f t (1 / (4 * (N : ℝ)))) :
    ∃ (f' : unitInterval → ℝ) (S : Set unitInterval),
      {t : unitInterval | f t ≥ m₀ - 1 / (N : ℝ)} ⊆ S ∧
      (∀ t, f' t ≤ f t) ∧
      (∀ t, t ∉ S → f' t = f t) ∧
      sSup (Set.range f') ≤ m₀ - 1 / (4 * (N : ℝ)) := by
  obtain ⟨C⟩ := OneDim.exists_refinement hf hm hN witness
  have hN_real : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN
  have hle : 1 / (4 * (N : ℝ)) ≤ 1 / (N : ℝ) := by
    apply one_div_le_one_div_of_le hN_real
    linarith
  obtain ⟨f', h_le, h_eq, h_sup⟩ :=
    exists_sup_reduction_of_cover hf hm hle C
  exact ⟨f', ⋃ l, C.piece l, C.covers_delta_near_critical, h_le, h_eq, h_sup⟩

end CombArg
