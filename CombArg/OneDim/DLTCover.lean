/-
Copyright (c) 2026 Xinze Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xinze Li
-/
import CombArg.Cover
import CombArg.Common.SavingClosure
import CombArg.OneDim.PartialRefinement
import Mathlib.Topology.Order.Compact

/-!
# `DLTCover` — the richer cover output of the DLT-style construction

The Stage A + B output of the DLT §3.2 Step 1 construction, packaged
as a first-class structure that exposes the spacing / refinement
data the abstract `FiniteCoverWithWitnesses` collapses into a plain
multiplicity bound. Geometric consumers (DLT modified-sweepout
blending, which requires positive-measure overlap on
`J_i ∩ J_{i+1}`) consume this type; pure scalar consumers can
downgrade via `DLTCover.toFinite`.

## Contents

* `DLTCover` — the structure: an `InitialCover` + a terminal
  `PartialRefinement` + `σ`-injectivity + the Stage-B termination
  invariant `∀ i, ic.I i ⊆ ⋃ k, pr.J k`.
* Convenience projections: `J`, `σ`, `wit`.
* `saving_on_J` — `f − E_{σ(k)} ≥ 1/(4N)` on the open piece `J k`.
* `saving_bound_closure` — same bound on `closure (J k)`, via
  continuity (`ge_of_closure_of_ge`).
* `twoFold_closure` — at most two pieces' closures contain any `t`,
  via `SkippedSpacedIntervals.not_three_overlap_any_order` plus
  `σ`-injectivity.
* `covers_nearCritical` — the open pieces `J k` cover the
  near-critical set.
* `toFinite` — downgrade to `FiniteCoverWithWitnesses` by taking
  closures of pieces and attaching uniform saving `1/(4N)`.

## Design rationale

See `paper/sections/intro.tex` Remark 1.5 (`rem:why-construction`)
and `docs/design-notes.md`. The abstract `FiniteCoverWithWitnesses`
suffices for the scalar Theorem 1.3 / sup-reduction Corollary 1.5
(see `CombArg.Scalar.Partition` for an alternative scalar proof
via partition-by-endpoints), but discards the positive-measure
overlap structure that DLT's modified-sweepout blending requires.
This file preserves that structure for forward compatibility with
GMT consumers under `CombArg.Geometric.*`.
-/

namespace CombArg.OneDim

open CombArg
open scoped Classical

variable {f : unitInterval → ℝ} {m₀ : ℝ} {N : ℕ}

/-! ## Structure -/

/-- **DLT-style cover output.** Produced by `exists_DLTCover` in
`CombArg/OneDim/Assembly.lean`. Packages the Stage A + B intermediate
state (initial cover + terminal partial refinement + σ-injectivity +
termination invariant) so that downstream geometric consumers can
access the spacing / overlap / witness-assignment structure directly.

Downgrade to `FiniteCoverWithWitnesses` via `toFinite` when only the
abstract scalar interface is needed. -/
@[ext] structure DLTCover
    (f : unitInterval → ℝ) (m₀ : ℝ) (N : ℕ) where
  /-- Underlying spaced + witness-bearing initial cover (Stage A). -/
  initialCover : InitialCover f m₀ N
  /-- Length of the refinement chain, i.e. number of refined pieces. -/
  L : ℕ
  /-- At least one piece. Forced by `initialCover.n_pos` plus the
  Stage-B termination invariant. -/
  L_pos : 0 < L
  /-- The Stage-B partial refinement: pieces `J_1, …, J_L`,
  index assignment `σ : Fin L → Fin initialCover.n`, with
  `J_subset` and `processed_cover` invariants. -/
  refinement : PartialRefinement initialCover L
  /-- σ-injectivity (Stage B termination output). -/
  σ_injective : Function.Injective refinement.σ
  /-- Stage-B terminal property: every initial-cover interval is
  covered by the refinement. -/
  initialCover_covered :
    ∀ i : Fin initialCover.n,
      initialCover.I i ⊆ ⋃ k : Fin L, refinement.J k

namespace DLTCover

variable (D : DLTCover f m₀ N)

/-! ## Convenience projections -/

/-- The `k`-th piece `J_k` of the refinement, as a subset of
`unitInterval`. Open in Case 1, open-minus-open (open) in Case 2. -/
@[reducible] def J (k : Fin D.L) : Set unitInterval := D.refinement.J k

/-- Witness-index assignment: the `k`-th refined piece is associated
with the `σ k`-th initial-cover interval (and the `σ k`-th witness). -/
@[reducible] def σ (k : Fin D.L) : Fin D.initialCover.n := D.refinement.σ k

/-- The `LocalWitness` attached to the `k`-th refined piece, namely
the `σ k`-th witness of the underlying `InitialCover`. -/
@[reducible] def wit (k : Fin D.L) :
    LocalWitness unitInterval f
      (D.initialCover.witnessCenter (D.σ k)) (1 / (4 * (N : ℝ))) :=
  D.initialCover.wit (D.σ k)

/-! ## Saving bound on the open piece and its closure -/

/-- The saving bound on the open piece `J k`, via the witness's
`saving_bound` lifted through `J_subset` and `I_subset_neighborhood`. -/
lemma saving_on_J (k : Fin D.L) (t : unitInterval) (ht : t ∈ D.J k) :
    f t - (D.wit k).replacementEnergy t ≥ 1 / (4 * (N : ℝ)) :=
  (D.wit k).saving_bound t
    (D.initialCover.I_subset_neighborhood (D.σ k)
      (D.refinement.J_subset k ht))

/-- **Saving-bound extends to closure via continuity.** For
`t ∈ closure (D.J k)`, the inequality
`f t − (D.wit k).replacementEnergy t ≥ 1/(4N)` holds, lifted from
the open piece via the shared `Common.sub_ge_of_closure` helper
(the level set `{s | 1/(4N) ≤ f s − E s}` is closed under continuity
of `f` and the witness's `replacementEnergy`). -/
lemma saving_bound_closure (hf : Continuous f)
    (k : Fin D.L) (t : unitInterval) (ht : t ∈ closure (D.J k)) :
    f t - (D.wit k).replacementEnergy t ≥ 1 / (4 * (N : ℝ)) :=
  sub_ge_of_closure hf (D.wit k).replacementEnergy_continuous
    (fun s hs => D.saving_on_J k s hs) ht

/-! ## TwoFold closure overlap (parity rescue) -/

/-- **TwoFold for the closure pieces**: every `t ∈ unitInterval` lies
in `closure (D.J k)` for at most two indices `k`. Combines
`σ`-injectivity with the parity-rescue lemma
`SkippedSpacedIntervals.not_three_overlap_any_order` on the
underlying spaced-intervals geometry. -/
lemma twoFold_closure (t : unitInterval) :
    (Finset.univ.filter
      (fun k : Fin D.L => t ∈ closure (D.J k))).card ≤ 2 := by
  by_contra h_not
  have h_gt : 2 < (Finset.univ.filter
      (fun k : Fin D.L => t ∈ closure (D.J k))).card := by omega
  obtain ⟨k1, k2, k3, hk1, hk2, hk3, hk12, hk13, hk23⟩ :=
    Finset.two_lt_card_iff.mp h_gt
  have h1 : t ∈ closure (D.J k1) := (Finset.mem_filter.mp hk1).2
  have h2 : t ∈ closure (D.J k2) := (Finset.mem_filter.mp hk2).2
  have h3 : t ∈ closure (D.J k3) := (Finset.mem_filter.mp hk3).2
  have h_clos_sub : ∀ k : Fin D.L,
      closure (D.J k) ⊆
        closure (D.initialCover.toSkippedSpacedIntervals.I (D.σ k)) :=
    fun k => closure_mono (D.refinement.J_subset k)
  have hd12v : (D.σ k1).val ≠ (D.σ k2).val :=
    fun h => hk12 (D.σ_injective (Fin.ext h))
  have hd13v : (D.σ k1).val ≠ (D.σ k3).val :=
    fun h => hk13 (D.σ_injective (Fin.ext h))
  have hd23v : (D.σ k2).val ≠ (D.σ k3).val :=
    fun h => hk23 (D.σ_injective (Fin.ext h))
  exact D.initialCover.toSkippedSpacedIntervals.not_three_overlap_any_order
    (D.σ k1) (D.σ k2) (D.σ k3) hd12v hd13v hd23v t
    (h_clos_sub k1 h1) (h_clos_sub k2 h2) (h_clos_sub k3 h3)

/-! ## Coverage of the near-critical set -/

/-- The open refined pieces `{J k}` cover the near-critical set. -/
lemma covers_nearCritical :
    nearCritical f m₀ N ⊆ ⋃ k : Fin D.L, D.J k := by
  calc nearCritical f m₀ N
      ⊆ ⋃ i : Fin D.initialCover.n, D.initialCover.I i :=
        D.initialCover.covers
    _ ⊆ ⋃ k : Fin D.L, D.refinement.J k :=
        Set.iUnion_subset D.initialCover_covered

/-! ## Downgrade to `FiniteCoverWithWitnesses` -/

/-- **Downgrade to the abstract scalar interface.** Take closures of
the open refined pieces, attach uniform saving `1/(4N)`, and use the
`σ k`-th witness's `replacementEnergy`. The two-fold bound, saving
bound, and coverage all transfer from the corresponding lemmas above.

This is the conversion used by `CombArg.OneDim.exists_refinement`:
the abstract scalar API is the composition `exists_DLTCover ∘ toFinite`.
The `hN : 0 < N` hypothesis is needed only for `saving_pos`. -/
noncomputable def toFinite (hf : Continuous f) (hN : 0 < N) :
    FiniteCoverWithWitnesses unitInterval f m₀
      (1 / (N : ℝ)) (1 / (4 * (N : ℝ))) where
  ι := Fin D.L
  ιFintype := inferInstance
  nonempty := ⟨⟨0, D.L_pos⟩⟩
  piece := fun k => closure (D.J k)
  replacementEnergy := fun k => (D.wit k).replacementEnergy
  saving := fun _ => 1 / (4 * (N : ℝ))
  saving_pos := fun _ => by
    have : (0 : ℝ) < N := Nat.cast_pos.mpr hN
    positivity
  saving_bound := fun k t ht => D.saving_bound_closure hf k t ht
  covers_delta_near_critical := by
    show {t : unitInterval | f t ≥ m₀ - 1 / (N : ℝ)}
        ⊆ ⋃ k : Fin D.L, closure (D.J k)
    calc {t : unitInterval | f t ≥ m₀ - 1 / (N : ℝ)}
        ⊆ ⋃ k : Fin D.L, D.J k := D.covers_nearCritical
      _ ⊆ ⋃ k : Fin D.L, closure (D.J k) :=
          Set.iUnion_mono (fun _ => subset_closure)
  twoFold := D.twoFold_closure
  saving_ge_eps := fun _ => le_refl _

end DLTCover

end CombArg.OneDim
