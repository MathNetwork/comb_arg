/-
Copyright (c) 2026 Xinze Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xinze Li
-/
import CombArg.Common.NearCritical
import CombArg.OneDim.SpacedIntervals
import CombArg.Witness
import Mathlib.Topology.UnitInterval

/-!
# Step 1 — Basic definitions

The paper's initial cover family. The near-critical set
`nearCritical` (and its closedness, compactness, nonemptiness
lemmas) lives in
[`CombArg.Common.NearCritical`](../Common/NearCritical.lean) and
is shared with the `Scalar.Partition` tier.

* `InitialCover` — DLT's `{I_i}` family, specialized to
  `K = unitInterval` per `docs/design-notes.md §4`, with explicit
  `intervalCenter` / `radius` / `witnessCenter` fields and the
  spacing-plus-subset invariants.
* `InitialCover.I` — the `i`-th interval as a subset of `unitInterval`.
* `exists_closedBall_subset_of_open` — auxiliary for working inside
  open neighborhoods on the unit interval.
-/

namespace CombArg.OneDim

open CombArg
open scoped Classical

/-- **Initial cover** — the DLT paper's `{I_i}` family.

Specialized to `K = unitInterval` (see `docs/design-notes.md §4`). The
`intervalCenter` / `witnessCenter` split is motivated in
`docs/design-notes.md §10`.

Corresponds to DLT (De Lellis–Tasnady 2013) Step 1, opening sentence:

> First of all we cover `K` with intervals
> `I_i = (t_i - η_i, t_i + η_i)` such that:
> **(a)** `t_i + η_i < t_{i+2} - η_{i+2}` for every `i`;
> **(b)** `t_i ∈ K` and `η_i < η_{t_i}`.

In the paper, a single `t_i` serves both as the **interval center**
(spacing condition (a)) and as the **LocalWitness center** (condition
(b)'s `η_{t_i}`). The formalization separates these two roles
(`intervalCenter i` vs `witnessCenter i`), linked by `I_subset_neighborhood`:
see `docs/design-notes.md §10` for the rationale (the existence proof
for a structure identifying both is intractable via Lebesgue number;
the separated form is paper-equivalent for the downstream induction).

The **saving is `1/(4N)` exactly**; this fixes the threshold the
refinement induction maintains through to
`FiniteCoverWithWitnesses.saving_ge_eps`. -/
@[ext] structure InitialCover
    (f : unitInterval → ℝ) (m₀ : ℝ) (N : ℕ)
    extends SkippedSpacedIntervals where
  /-- At least one interval — needed for the induction's base case
  `J_1 := I_1`. -/
  n_pos : 0 < n
  /-- The base point in `nearCritical f m₀ N` at which the `i`-th
  `LocalWitness` lives. Paper's `t_i` in its condition (b) role. -/
  witnessCenter : Fin n → unitInterval
  /-- Each witness center is in the near-critical set. -/
  witnessCenter_mem_nearCritical : ∀ i, witnessCenter i ∈ nearCritical f m₀ N
  /-- `LocalWitness` at the `i`-th witness center with saving exactly
  `1/(4N)`. -/
  wit : (i : Fin n) →
    LocalWitness unitInterval f (witnessCenter i) (1 / (4 * (N : ℝ)))
  /-- **DLT condition (b)** — each interval `I_i` lies inside the
  `i`-th witness neighborhood. In the paper a single `t_i` serves
  as both interval center and witness center and the condition
  reads `η_i < η_{t_i}`; here we decouple and state the
  downstream-usable subset directly. -/
  I_subset_neighborhood : ∀ i : Fin n,
      openInterval (intervalCenter i) (radius i) ⊆ (wit i).neighborhood
  /-- The `I_i = (intervalCenter i - η_i, intervalCenter i + η_i) ∩ [0,1]`
  together cover the near-critical set. -/
  covers :
      nearCritical f m₀ N ⊆
        ⋃ i : Fin n, openInterval (intervalCenter i) (radius i)

section InitialCoverLemmas

variable {f : unitInterval → ℝ} {m₀ : ℝ} {N : ℕ}

/-- The `i`-th interval `I_i` of an initial cover, as a subset of
`unitInterval`. Inherits from the underlying `SkippedSpacedIntervals`
via the auto-generated `toSkippedSpacedIntervals` projection. -/
@[reducible] def InitialCover.I
    (ic : InitialCover f m₀ N) (i : Fin ic.n) : Set unitInterval :=
  ic.toSkippedSpacedIntervals.I i

end InitialCoverLemmas

/-! ## Auxiliary: closed ball inside an open set on `unitInterval` -/

/-- For an open set `U` containing `t` in `unitInterval`, there exists a
positive radius `δ` such that the closed `δ`-ball around `t` in the
subtype metric is contained in `U`. -/
lemma exists_closedBall_subset_of_open
    {U : Set unitInterval} (hU : IsOpen U) {t : unitInterval} (ht : t ∈ U) :
    ∃ δ > 0, Metric.closedBall t δ ⊆ U := by
  rw [Metric.isOpen_iff] at hU
  obtain ⟨ε, hε_pos, hε⟩ := hU t ht
  refine ⟨ε / 2, half_pos hε_pos, fun s hs => hε ?_⟩
  simp only [Metric.mem_closedBall] at hs
  simp only [Metric.mem_ball]
  linarith

end CombArg.OneDim
