/-
Copyright (c) 2026 Xinze Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xinze Li
-/
import CombArg.Cover
import CombArg.Scalar.Partition.WitnessSelection
import CombArg.Scalar.Partition.Multiplicity
import CombArg.Scalar.Partition.Coverage

/-!
# `CombArg.Scalar.Partition` — partition-by-endpoints proof of the abstract scalar theorem

A self-contained alternative to `CombArg.OneDim.exists_refinement`
that bypasses the DLT-style overlapping cover. The output type is
the same abstract `FiniteCoverWithWitnesses unitInterval f m₀ (1/N) (1/(4N))`,
but the construction discards the spacing / overlap structure that
the DLT route preserves; this proof is therefore unsuitable as the
input to a geometric modified-sweepout lift (which requires
positive-measure overlap on `J_i ∩ J_{i+1}`). See
`paper/sections/intro.tex` Remark 1.5 for the design rationale.

## Construction outline

Let `f : unitInterval → ℝ` be continuous, `m₀ = sSup (range f)`,
`N > 0`, and let a `LocalWitness` be supplied at every
`1/N`-near-critical parameter.

1. **Compactness** of `nearCritical f m₀ N` (closed subset of compact
   `unitInterval`) gives, together with the witness hypothesis, a
   finite open cover by `coverIvl tk = Subtype.val ⁻¹' Ioo a_tk b_tk`
   (`Partition/CoverIvl`).
2. By `IsCompact.elim_finite_subcover`, reduce to a finite indexing
   `T : Finset (nearCritical f m₀ N)` with `nearCritical ⊆ ⋃ tk ∈ T,
   coverIvl tk`.
3. Form the endpoint Finset `E : Finset ℝ` containing `0`, `1`, and
   all `a_tk, b_tk` for `tk ∈ T`. Sort to a list `[e₀, …, e_M]`
   (`Partition/Endpoints`).
4. The pieces are `q_j := Subtype.val ⁻¹' Icc e_j e_{j+1}` for
   `j : Fin (M-1)` (`Partition/Pieces`); they have multiplicity
   `≤ 2` (`Partition/Multiplicity`) and cover `unitInterval`
   (`Partition/Coverage`).
5. For each piece intersecting `nearCritical`, a covering witness
   `tk ∈ T` is selected such that the piece sits inside its
   `Icc`-preimage (`Partition/WitnessSelection`).
6. The output cover indexes the assembly by the **subtype** of
   indices whose piece intersects `nearCritical`, eliminating empty
   pieces and conditional witness assignment.

## Module layout

* [`Helpers`](Partition/Helpers.lean) — closure inclusion + open Ioo
  extraction (subspace topology).
* [`CoverIvl`](Partition/CoverIvl.lean) — per-witness `(a, b)`
  bounds and the Ioo-preimage open cover of `nearCritical`.
* [`Endpoints`](Partition/Endpoints.lean) — endpoint Finset, sort to
  a strictly-increasing list, membership iff.
* [`Pieces`](Partition/Pieces.lean) — partition pieces between
  consecutive sorted endpoints.
* [`WitnessSelection`](Partition/WitnessSelection.lean) — for each
  piece intersecting `nearCritical`, pick a covering witness.
* [`Multiplicity`](Partition/Multiplicity.lean) — pieces have
  multiplicity `≤ 2`.
* [`Coverage`](Partition/Coverage.lean) — the pieces cover
  `unitInterval`, hence `nearCritical`.

The main theorem `exists_refinement_partition` lives in this file
and assembles the components into the final
`FiniteCoverWithWitnesses` output.
-/

namespace CombArg.Scalar

open CombArg CombArg.OneDim CombArg.Scalar.Partition
open scoped Classical

variable {f : unitInterval → ℝ} {m₀ : ℝ} {N : ℕ}

/-! ## Subtype-indexed assembly

Only those `Fin ((endpts T).card - 1)` indices whose corresponding
piece intersects `nearCritical` are wrapped into the
`FiniteCoverWithWitnesses` cover. The subtype-indexed cover has no
empty pieces, no conditional witness assignment, and each piece
inherits its multiplicity bound directly from
`piece_multiplicity_le_two`. -/

variable
  (witness : ∀ t : unitInterval, f t ≥ m₀ - 1 / (N : ℝ) →
                LocalWitness unitInterval f t (1 / (4 * (N : ℝ))))

/-- Subtype of `Fin ((endpts T).card - 1)` selecting only the
indices whose piece intersects `nearCritical f m₀ N`. -/
private abbrev coveredIndex
    (T : Finset ↥(nearCritical f m₀ N)) : Type :=
  {j : Fin ((endpts witness T).card - 1) //
    (piece witness T j ∩ nearCritical f m₀ N).Nonempty}

/-- For a covered index, choose a covering witness via
`exists_witness_for_piece`. -/
private noncomputable def chosenTk
    (T : Finset ↥(nearCritical f m₀ N))
    (hT : nearCritical f m₀ N ⊆ ⋃ tk ∈ T, coverIvl witness tk)
    (jh : coveredIndex witness T) : ↥(nearCritical f m₀ N) :=
  (exists_witness_for_piece witness hT
    jh.property.choose_spec.1 jh.property.choose_spec.2).choose

/-- The chosen witness's `Icc`-preimage contains the piece. -/
private lemma chosenTk_piece_subset
    (T : Finset ↥(nearCritical f m₀ N))
    (hT : nearCritical f m₀ N ⊆ ⋃ tk ∈ T, coverIvl witness tk)
    (jh : coveredIndex witness T) :
    piece witness T jh.val ⊆
      Subtype.val ⁻¹' Set.Icc (bounds witness (chosenTk witness T hT jh)).1
                              (bounds witness (chosenTk witness T hT jh)).2 :=
  (exists_witness_for_piece witness hT
    jh.property.choose_spec.1 jh.property.choose_spec.2).choose_spec.2

/-- Saving bound on the piece corresponding to a covered index.
On the open `Ioo` interior the witness's `saving_bound` gives
`f − E ≥ 1/(4N)`; the closed-piece bound follows by
`mem_closure_val_preimage_Ioo` plus `IsClosed.closure_subset_iff`
on the level set `{s | 1/(4N) ≤ f s − E s}`. -/
private lemma chosenTk_saving_bound
    (hf : Continuous f)
    (T : Finset ↥(nearCritical f m₀ N))
    (hT : nearCritical f m₀ N ⊆ ⋃ tk ∈ T, coverIvl witness tk)
    (jh : coveredIndex witness T) :
    ∀ t ∈ piece witness T jh.val,
      f t - (witness (chosenTk witness T hT jh).val
                     (chosenTk witness T hT jh).property).replacementEnergy t
        ≥ 1 / (4 * (N : ℝ)) := by
  intro t ht
  set tk := chosenTk witness T hT jh
  have h_t_in_Icc : t.val ∈
      Set.Icc (bounds witness tk).1 (bounds witness tk).2 :=
    chosenTk_piece_subset witness T hT jh ht
  have h_bspec := bounds_spec witness tk
  have h_a_lt_one : (bounds witness tk).1 < 1 := by
    have h_lt : (bounds witness tk).1 < tk.val.val := h_bspec.1
    have h_le : tk.val.val ≤ 1 := tk.val.2.2
    linarith
  have h_b_pos : 0 < (bounds witness tk).2 := by
    have h_lt : tk.val.val < (bounds witness tk).2 := h_bspec.2.1
    have h_ge : 0 ≤ tk.val.val := tk.val.2.1
    linarith
  have h_a_lt_b : (bounds witness tk).1 < (bounds witness tk).2 :=
    lt_trans h_bspec.1 h_bspec.2.1
  have h_sav_Ioo : ∀ s : unitInterval,
      s.val ∈ Set.Ioo (bounds witness tk).1 (bounds witness tk).2 →
        f s - (witness tk.val tk.property).replacementEnergy s ≥
          1 / (4 * (N : ℝ)) := fun s hs =>
    (witness tk.val tk.property).saving_bound s (h_bspec.2.2 hs)
  have h_t_closure :
      t ∈ closure (Subtype.val ⁻¹' Set.Ioo
        (bounds witness tk).1 (bounds witness tk).2 : Set unitInterval) :=
    mem_closure_val_preimage_Ioo h_a_lt_one h_b_pos h_a_lt_b h_t_in_Icc
  exact (isClosed_le continuous_const
    (hf.sub (witness tk.val tk.property).replacementEnergy_continuous)
    ).closure_subset_iff.mpr h_sav_Ioo h_t_closure

/-- The covered-index pieces cover `nearCritical`. -/
private lemma coveredIndex_covers
    (T : Finset ↥(nearCritical f m₀ N)) :
    nearCritical f m₀ N ⊆
      ⋃ jh : coveredIndex witness T, piece witness T jh.val := by
  intro t ht
  obtain ⟨j, hj⟩ := exists_piece_containing witness T t
  have h_inter : (piece witness T j ∩ nearCritical f m₀ N).Nonempty :=
    ⟨t, hj, ht⟩
  exact Set.mem_iUnion.mpr ⟨⟨j, h_inter⟩, hj⟩

/-- Multiplicity bound on the covered-index pieces.
Pieces inject into the underlying `Fin ((endpts T).card - 1)` filter
via `Subtype.val`, and the image is contained in the
`piece_multiplicity_le_two` filter. Cardinality is preserved by
injectivity. -/
private lemma coveredIndex_twoFold
    (T : Finset ↥(nearCritical f m₀ N)) (t : unitInterval) :
    (Finset.univ.filter
      (fun jh : coveredIndex witness T =>
        t ∈ piece witness T jh.val)).card ≤ 2 := by
  set S : Finset (coveredIndex witness T) := Finset.univ.filter
    (fun jh => t ∈ piece witness T jh.val)
  have h_inj : Function.Injective
      (Subtype.val : coveredIndex witness T → Fin _) :=
    Subtype.val_injective
  have h_card_eq : S.card = (S.image Subtype.val).card :=
    (Finset.card_image_of_injective _ h_inj).symm
  rw [h_card_eq]
  refine le_trans (Finset.card_le_card ?_)
    (piece_multiplicity_le_two witness T t)
  intro j hj
  obtain ⟨jh, hjh, rfl⟩ := Finset.mem_image.mp hj
  rw [Finset.mem_filter] at hjh ⊢
  exact ⟨Finset.mem_univ _, hjh.2⟩

/-! ## Main theorem -/

/-- **Partition-by-endpoints proof of the abstract scalar Theorem 1.3.**

Same conclusion as `CombArg.OneDim.exists_refinement`, but proved by
the cheaper compactness + endpoint-partition argument that discards
the DLT-style overlap structure. The output cover is unsuitable as
input for a geometric modified-sweepout lift (which requires
positive-measure overlap on `J_i ∩ J_{i+1}`); for that, use the
DLT-faithful `OneDim.exists_DLTCover` / `OneDim.exists_refinement`.
See `paper/sections/intro.tex` Remark 1.5 for the design rationale.

Construction:
1. `IsCompact.elim_finite_subcover` on `nearCritical f m₀ N` and the
   open `Ioo`-preimages around each near-critical witness center.
2. The endpoints `{0, 1, (bounds tk).1, (bounds tk).2 : tk ∈ T}` are
   sorted; each pair of consecutive sorted endpoints defines a closed
   piece in `unitInterval`.
3. For each piece intersecting `nearCritical`, a witness is selected
   such that the piece sits inside its `Icc`-preimage; the saving
   bound on the open `Ioo` extends to the closed piece via continuity.
4. Multiplicity `≤ 2` follows from the strict monotonicity of the
   sorted list (consecutive pieces share only an endpoint;
   non-consecutive are disjoint).
5. The output cover is indexed by a subtype selecting only those
   pieces that intersect `nearCritical`, dropping the empties. -/
theorem exists_refinement_partition
    (hf : Continuous f) (hm : m₀ = sSup (Set.range f)) (hN : 0 < N)
    (witness_data : ∀ t : unitInterval, f t ≥ m₀ - 1 / (N : ℝ) →
                      LocalWitness unitInterval f t (1 / (4 * (N : ℝ)))) :
    Nonempty (FiniteCoverWithWitnesses unitInterval f m₀
              (1 / (N : ℝ)) (1 / (4 * (N : ℝ)))) := by
  -- Compactness + finite open subcover.
  have hKcomp : IsCompact (nearCritical f m₀ N) := isCompact_nearCritical hf
  obtain ⟨T, hT⟩ := hKcomp.elim_finite_subcover (coverIvl witness_data)
    (isOpen_coverIvl witness_data) (coverIvl_covers_nearCritical witness_data)
  -- `nearCritical` is non-empty (uses `hm` and `hN`); pick a witness point
  -- to show the covered-index subtype is non-empty.
  have hNC_ne : (nearCritical f m₀ N).Nonempty := nearCritical_nonempty hf hm hN
  obtain ⟨t_NC, ht_NC⟩ := hNC_ne
  obtain ⟨j₀, hj₀⟩ := exists_piece_containing witness_data T t_NC
  refine ⟨{
    ι := coveredIndex witness_data T
    ιFintype := inferInstance
    nonempty := ⟨⟨j₀, ⟨t_NC, hj₀, ht_NC⟩⟩⟩
    piece := fun jh => piece witness_data T jh.val
    replacementEnergy := fun jh =>
      (witness_data (chosenTk witness_data T hT jh).val
                    (chosenTk witness_data T hT jh).property).replacementEnergy
    saving := fun _ => 1 / (4 * (N : ℝ))
    saving_pos := fun _ => by
      have : (0 : ℝ) < N := Nat.cast_pos.mpr hN
      positivity
    saving_ge_eps := fun _ => le_refl _
    saving_bound := chosenTk_saving_bound witness_data hf T hT
    covers_delta_near_critical := coveredIndex_covers witness_data T
    twoFold := coveredIndex_twoFold witness_data T }⟩

end CombArg.Scalar
