/-
Copyright (c) 2026 Xinze Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xinze Li
-/
import CombArg.OneDim.SpacedIntervals
import CombArg.Witness
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.UnitInterval

/-!
# Step 1 — Basic definitions

The near-critical set and the paper's initial cover family.

* `nearCritical` — the `1/N`-near-critical set and its closedness,
  compactness, nonemptiness properties.
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

section GenericK

variable {K : Type*} [TopologicalSpace K]
    {f : K → ℝ} {m₀ : ℝ} {N : ℕ}

/-- The `1/N`-near-critical set of `f` with respect to `m₀`. -/
def nearCritical (f : K → ℝ) (m₀ : ℝ) (N : ℕ) : Set K :=
  {t : K | f t ≥ m₀ - 1 / (N : ℝ)}

omit [TopologicalSpace K] in
/-- Membership in `nearCritical` unfolds to the defining inequality
`f t ≥ m₀ - 1/N`. Holds without a topological structure on `K`. -/
lemma mem_nearCritical {t : K} :
    t ∈ nearCritical f m₀ N ↔ f t ≥ m₀ - 1 / (N : ℝ) := Iff.rfl

/-- The near-critical set is closed: it is the preimage of the closed
half-line `[m₀ - 1/N, ∞)` under continuous `f`. -/
lemma isClosed_nearCritical (hf : Continuous f) :
    IsClosed (nearCritical f m₀ N) :=
  isClosed_le continuous_const hf

/-- The near-critical set is compact: closed subset of compact `K`. -/
lemma isCompact_nearCritical [CompactSpace K] (hf : Continuous f) :
    IsCompact (nearCritical f m₀ N) :=
  (isClosed_nearCritical hf).isCompact

/-- The near-critical set is nonempty: a maximizer of `f` on `K` attains
`m₀ = sSup (range f)` and hence satisfies `f t₀ ≥ m₀ - 1/N`. -/
lemma nearCritical_nonempty [CompactSpace K] [Nonempty K]
    (hf : Continuous f) (hm : m₀ = sSup (Set.range f)) (hN : 0 < N) :
    (nearCritical f m₀ N).Nonempty := by
  obtain ⟨t₀, _, ht₀⟩ :=
    isCompact_univ.exists_isMaxOn Set.univ_nonempty hf.continuousOn
  refine ⟨t₀, ?_⟩
  show f t₀ ≥ m₀ - 1 / (N : ℝ)
  have hle : m₀ ≤ f t₀ := by
    rw [hm]
    refine csSup_le ⟨f t₀, Set.mem_range_self _⟩ ?_
    rintro x ⟨t, rfl⟩
    exact ht₀ (Set.mem_univ t)
  have hinv : (0 : ℝ) < 1 / (N : ℝ) :=
    one_div_pos.mpr (Nat.cast_pos.mpr hN)
  linarith

end GenericK

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
structure InitialCover
    (f : unitInterval → ℝ) (m₀ : ℝ) (N : ℕ) where
  /-- Number of intervals `I_i` in the cover. -/
  n : ℕ
  /-- At least one interval — needed for the induction's base case
  `J_1 := I_1`. -/
  n_pos : 0 < n
  /-- The center of the `i`-th interval `I_i`. Need **not** itself
  lie in `nearCritical f m₀ N`; free to be any point of `unitInterval`.
  Spacing condition (a) is about these centers. -/
  intervalCenter : Fin n → unitInterval
  /-- The radius `η_i > 0` of each interval (DLT's `η_i`). -/
  radius : Fin n → ℝ
  /-- Strict positivity of each radius. -/
  radius_pos : ∀ i, 0 < radius i
  /-- The base point in `nearCritical f m₀ N` at which the `i`-th
  `LocalWitness` lives. Paper's `t_i` in its condition (b) role. -/
  witnessCenter : Fin n → unitInterval
  /-- Each witness center is in the near-critical set. -/
  witnessCenter_mem_nearCritical : ∀ i, witnessCenter i ∈ nearCritical f m₀ N
  /-- `LocalWitness` at the `i`-th witness center with saving exactly
  `1/(4N)`. -/
  wit : (i : Fin n) →
    LocalWitness unitInterval f (witnessCenter i) (1 / (4 * (N : ℝ)))
  /-- **DLT condition (a)** — strict non-overlap between non-adjacent
  intervals, stated on `intervalCenter`:
  `intervalCenter i + η_i < intervalCenter (i+2) - η_{i+2}` for every
  valid `i`. -/
  two_fold_spacing : ∀ (i : Fin n) (h : i.val + 2 < n),
      (intervalCenter i).val + radius i <
        (intervalCenter ⟨i.val + 2, h⟩).val - radius ⟨i.val + 2, h⟩
  /-- **DLT condition (b)** — each interval `I_i` lies inside the
  `i`-th witness neighborhood. In the paper a single `t_i` serves as
  both interval center and witness center and the condition reads
  `η_i < η_{t_i}`; here we decouple and state the downstream-usable
  subset directly. -/
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
`unitInterval`. Convenience abbreviation. -/
def InitialCover.I
    (ic : InitialCover f m₀ N) (i : Fin ic.n) : Set unitInterval :=
  openInterval (ic.intervalCenter i) (ic.radius i)

/-- The geometric part of an `InitialCover`: the skip-2 spaced
open intervals on `unitInterval`, forgetting the witness centers,
local witnesses, and coverage of `nearCritical`. The disjointness
lemmas in `CombArg.OneDim.Disjointness` delegate to this
projection. -/
def InitialCover.toSkippedSpacedIntervals
    (ic : InitialCover f m₀ N) : SkippedSpacedIntervals where
  n := ic.n
  intervalCenter := ic.intervalCenter
  radius := ic.radius
  radius_pos := ic.radius_pos
  two_fold_spacing := ic.two_fold_spacing

/-- The `I`-field on `InitialCover` agrees with the `I`-field on
its `SkippedSpacedIntervals` projection (definitional). -/
lemma InitialCover.toSkippedSpacedIntervals_I
    (ic : InitialCover f m₀ N) (i : Fin ic.n) :
    ic.toSkippedSpacedIntervals.I i = ic.I i := rfl

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
