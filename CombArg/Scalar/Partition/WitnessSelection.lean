/-
Copyright (c) 2026 Xinze Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xinze Li
-/
import CombArg.Scalar.Partition.Pieces

/-!
# `CombArg.Scalar.Partition.WitnessSelection` — per-piece witness picking

For each partition piece `q_j` whose interior intersects `nearCritical`,
some witness in `T` covers the entire closed piece. The argument: a
point `t ∈ q_j ∩ nearCritical` lies in some `coverIvl tk = val⁻¹(Ioo a_{tk} b_{tk})`,
so `a_{tk} < t.val < b_{tk}`. Both `a_{tk}` and `b_{tk}` are in the
sorted endpoint list (no other endpoint can lie strictly between
`pieceLo j` and `pieceHi j`, since these are consecutive sorted), so
`a_{tk} ≤ pieceLo j` and `pieceHi j ≤ b_{tk}`. Hence
`q_j ⊆ val⁻¹(Icc a_{tk} b_{tk})`.
-/

namespace CombArg.Scalar.Partition

open CombArg CombArg.OneDim
open scoped Classical

variable {f : unitInterval → ℝ} {m₀ : ℝ} {N : ℕ}
variable
  (witness : ∀ t : unitInterval, f t ≥ m₀ - 1 / (N : ℝ) →
                LocalWitness unitInterval f t (1 / (4 * (N : ℝ))))

/-- The witness selection lemma: for any piece intersecting
`nearCritical`, some `tk ∈ T` has the piece inside its `Icc`-preimage. -/
lemma exists_witness_for_piece
    {T : Finset ↥(nearCritical f m₀ N)}
    (hT : nearCritical f m₀ N ⊆ ⋃ tk ∈ T, coverIvl witness tk)
    {j : Fin ((endpts witness T).card - 1)}
    {t : unitInterval}
    (ht_piece : t ∈ piece witness T j)
    (ht_NC : t ∈ nearCritical f m₀ N) :
    ∃ tk ∈ T, piece witness T j ⊆
      Subtype.val ⁻¹' Set.Icc (bounds witness tk).1 (bounds witness tk).2 := by
  -- Step A: locate `tk ∈ T` with `t ∈ coverIvl tk`.
  obtain ⟨tk, htk_mem, ht_cov⟩ : ∃ tk ∈ T, t ∈ coverIvl witness tk := by
    have h_t_in_union : t ∈ ⋃ tk ∈ T, coverIvl witness tk := hT ht_NC
    obtain ⟨tk, htk_mem, ht_cov⟩ := Set.mem_iUnion₂.mp h_t_in_union
    exact ⟨tk, htk_mem, ht_cov⟩
  refine ⟨tk, htk_mem, ?_⟩
  -- Step B: get strict inequalities from `coverIvl`.
  have ht_a : (bounds witness tk).1 < t.val := ht_cov.1
  have ht_b : t.val < (bounds witness tk).2 := ht_cov.2
  -- Step C: get piece bounds on `t.val`.
  rw [mem_piece_iff] at ht_piece
  obtain ⟨ht_lo, ht_hi⟩ := ht_piece
  -- Step D: locate indices of `(bounds tk).1, .2` in the sorted list.
  obtain ⟨ia, hia_eq⟩ := exists_index_of_bounds_left witness htk_mem
  obtain ⟨ib, hib_eq⟩ := exists_index_of_bounds_right witness htk_mem
  -- Step E: bound facts on the sorted-list indices.
  have hL : (sortedEndpts witness T).length = (endpts witness T).card :=
    sortedEndpts_length witness T
  have h2 : 2 ≤ (endpts witness T).card := endpts_card_ge_two witness T
  have hj : j.val < (endpts witness T).card - 1 := j.isLt
  have h_jLo_lt_len : j.val < (sortedEndpts witness T).length := by omega
  have h_jHi_lt_len : j.val + 1 < (sortedEndpts witness T).length := by omega
  -- Sorted-list `get` at the piece's bracket-indices reduces to
  -- `pieceLo` / `pieceHi` definitionally.
  have h_lo_eq :
      (sortedEndpts witness T).get ⟨j.val, h_jLo_lt_len⟩ = pieceLo witness T j :=
    rfl
  have h_hi_eq :
      (sortedEndpts witness T).get ⟨j.val + 1, h_jHi_lt_len⟩ =
        pieceHi witness T j := rfl
  -- Step F: monotonicity of `get`.
  have h_smono : StrictMono (sortedEndpts witness T).get :=
    sortedEndpts_sortedLT witness T
  -- Step G: `ia.val < j.val + 1`. From `get ia = bounds.1 < t.val ≤ get jHi`
  -- and strict monotonicity (contrapositive form `≤ → ≤`).
  have h_ia_lt_succ : ia.val < j.val + 1 := by
    by_contra h_not
    have h_le : (sortedEndpts witness T).get ⟨j.val + 1, h_jHi_lt_len⟩
                  ≤ (sortedEndpts witness T).get ia :=
      h_smono.le_iff_le.mpr (not_lt.mp h_not)
    rw [h_hi_eq, hia_eq] at h_le
    linarith
  have h_a_le_pieceLo : (bounds witness tk).1 ≤ pieceLo witness T j := by
    rw [← hia_eq, ← h_lo_eq]
    refine h_smono.le_iff_le.mpr ?_
    show ia.val ≤ j.val
    omega
  -- Step H: `j.val < ib.val`.
  have h_j_lt_ib : j.val < ib.val := by
    by_contra h_not
    have h_le : (sortedEndpts witness T).get ib
                  ≤ (sortedEndpts witness T).get ⟨j.val, h_jLo_lt_len⟩ :=
      h_smono.le_iff_le.mpr (not_lt.mp h_not)
    rw [hib_eq, h_lo_eq] at h_le
    linarith
  have h_pieceHi_le_b : pieceHi witness T j ≤ (bounds witness tk).2 := by
    rw [← h_hi_eq, ← hib_eq]
    refine h_smono.le_iff_le.mpr ?_
    show j.val + 1 ≤ ib.val
    omega
  -- Step I: conclude `piece ⊆ val⁻¹(Icc a b)`.
  intro s hs
  rw [mem_piece_iff] at hs
  rw [Set.mem_preimage, Set.mem_Icc]
  exact ⟨le_trans h_a_le_pieceLo hs.1, le_trans hs.2 h_pieceHi_le_b⟩

end CombArg.Scalar.Partition
