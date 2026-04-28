/-
Copyright (c) 2026 Xinze Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xinze Li
-/
import CombArg.Scalar.Partition.Pieces

/-!
# `CombArg.Scalar.Partition.Coverage` — coverage of `unitInterval`

The pieces `{piece j : j ∈ Fin (M-1)}` cover the entire `unitInterval`,
hence in particular cover `nearCritical`. The argument: for any
`t : unitInterval`, take `j_max` to be the largest index in
`Fin (M-1)` with `pieceLo j_max ≤ t.val`. Such an index exists because
`pieceLo ⟨0, _⟩ = sortedEndpts[0] ≤ 0 ≤ t.val` (since `0 ∈ endpts`).
And `t.val ≤ pieceHi j_max` because either `j_max.val + 1 < M - 1`,
in which case maximality forces the next index to fail
`pieceLo ≤ t.val`; or `j_max.val = M - 2`, in which case `pieceHi j_max
= sortedEndpts[M-1] ≥ 1 ≥ t.val` (since `1 ∈ endpts`).
-/

namespace CombArg.Scalar.Partition

open CombArg CombArg.OneDim
open scoped Classical

variable {f : unitInterval → ℝ} {m₀ : ℝ} {N : ℕ}
variable
  (witness : ∀ t : unitInterval, f t ≥ m₀ - 1 / (N : ℝ) →
                LocalWitness unitInterval f t (1 / (4 * (N : ℝ))))

/-- The smallest sorted endpoint is `≤ 0`. -/
lemma sortedEndpts_first_le_zero
    (T : Finset ↥(nearCritical f m₀ N))
    (h0 : 0 < (sortedEndpts witness T).length) :
    (sortedEndpts witness T).get ⟨0, h0⟩ ≤ 0 := by
  have h_smono : StrictMono (sortedEndpts witness T).get :=
    sortedEndpts_sortedLT witness T
  have h0_endpts : (0 : ℝ) ∈ endpts witness T := Finset.mem_insert_self _ _
  have h0_L : (0 : ℝ) ∈ sortedEndpts witness T :=
    (mem_sortedEndpts_iff witness T 0).mpr h0_endpts
  obtain ⟨k0, hk0⟩ := List.mem_iff_get.mp h0_L
  rw [← hk0]
  exact h_smono.le_iff_le.mpr (Nat.zero_le _)

/-- The largest sorted endpoint is `≥ 1`. -/
lemma sortedEndpts_last_ge_one
    (T : Finset ↥(nearCritical f m₀ N)) :
    1 ≤ (sortedEndpts witness T).get
            ⟨(sortedEndpts witness T).length - 1, by
              have h2 : 2 ≤ (endpts witness T).card :=
                endpts_card_ge_two witness T
              have hL : (sortedEndpts witness T).length =
                (endpts witness T).card := sortedEndpts_length witness T
              omega⟩ := by
  have h_smono : StrictMono (sortedEndpts witness T).get :=
    sortedEndpts_sortedLT witness T
  have hL : (sortedEndpts witness T).length = (endpts witness T).card :=
    sortedEndpts_length witness T
  have h2 : 2 ≤ (endpts witness T).card := endpts_card_ge_two witness T
  have h1_endpts : (1 : ℝ) ∈ endpts witness T := by
    unfold endpts
    exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have h1_L : (1 : ℝ) ∈ sortedEndpts witness T :=
    (mem_sortedEndpts_iff witness T 1).mpr h1_endpts
  obtain ⟨k1, hk1⟩ := List.mem_iff_get.mp h1_L
  rw [show (1 : ℝ) = (sortedEndpts witness T).get k1 from hk1.symm]
  refine h_smono.le_iff_le.mpr ?_
  show k1.val ≤ (sortedEndpts witness T).length - 1
  have := k1.isLt
  omega

/-- **Coverage**: every `t : unitInterval` lies in some piece. -/
lemma exists_piece_containing
    (T : Finset ↥(nearCritical f m₀ N)) (t : unitInterval) :
    ∃ j : Fin ((endpts witness T).card - 1), t ∈ piece witness T j := by
  have hL : (sortedEndpts witness T).length = (endpts witness T).card :=
    sortedEndpts_length witness T
  have h2 : 2 ≤ (endpts witness T).card := endpts_card_ge_two witness T
  have h_smono : StrictMono (sortedEndpts witness T).get :=
    sortedEndpts_sortedLT witness T
  have h_t_nonneg : (0 : ℝ) ≤ t.val := t.2.1
  have h_t_le_one : t.val ≤ 1 := t.2.2
  -- Set S of valid Fin (M-1) indices i with pieceLo i ≤ t.val.
  let S : Finset (Fin ((endpts witness T).card - 1)) :=
    Finset.univ.filter (fun i => pieceLo witness T i ≤ t.val)
  have hS_ne : S.Nonempty := by
    refine ⟨⟨0, by omega⟩, ?_⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    show pieceLo witness T ⟨0, by omega⟩ ≤ t.val
    have h_first : (sortedEndpts witness T).get
        ⟨0, by have := h2; omega⟩ ≤ 0 :=
      sortedEndpts_first_le_zero witness T (by have := h2; omega)
    have h_eq : pieceLo witness T ⟨0, by omega⟩ =
        (sortedEndpts witness T).get ⟨0, by have := h2; omega⟩ := rfl
    linarith
  let j_max := S.max' hS_ne
  refine ⟨j_max, ?_⟩
  have hj_max_in_S : j_max ∈ S := S.max'_mem hS_ne
  have h_lo_le : pieceLo witness T j_max ≤ t.val :=
    (Finset.mem_filter.mp hj_max_in_S).2
  rw [mem_piece_iff]
  refine ⟨h_lo_le, ?_⟩
  -- Need t.val ≤ pieceHi witness T j_max.
  -- Case on whether j_max.val + 1 < (endpts witness T).card - 1.
  by_cases h_succ_lt : j_max.val + 1 < (endpts witness T).card - 1
  · -- Successor `j_next` is a valid index in `Fin (M-1)`.
    -- `j_next > j_max`, so `j_next ∉ S` (else it would beat `j_max`).
    -- Hence `pieceLo j_next > t.val`. But `pieceLo j_next = pieceHi j_max`.
    let j_next : Fin ((endpts witness T).card - 1) :=
      ⟨j_max.val + 1, h_succ_lt⟩
    have h_j_next_not_le : ¬ j_next ≤ j_max := by
      intro h_le
      have h_val_le : j_max.val + 1 ≤ j_max.val := h_le
      omega
    have h_j_next_not_in_S : j_next ∉ S := fun hin =>
      h_j_next_not_le (S.le_max' j_next hin)
    have h_pieceLo_gt : t.val < pieceLo witness T j_next := by
      by_contra h_not
      exact h_j_next_not_in_S
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, not_lt.mp h_not⟩)
    -- `pieceHi j_max = pieceLo j_next` by definitional equality.
    show t.val ≤ pieceHi witness T j_max
    have h_eq : pieceHi witness T j_max = pieceLo witness T j_next := rfl
    linarith
  · -- j_max.val = M - 2, so pieceHi j_max = sortedEndpts[M-1] ≥ 1 ≥ t.val.
    have h_eq_M_minus_2 : j_max.val = (endpts witness T).card - 2 := by
      have := j_max.isLt
      omega
    have h_jhi_eq_last : pieceHi witness T j_max =
        (sortedEndpts witness T).get
          ⟨(sortedEndpts witness T).length - 1, by omega⟩ := by
      show (sortedEndpts witness T).get ⟨j_max.val + 1, by omega⟩ =
        (sortedEndpts witness T).get
          ⟨(sortedEndpts witness T).length - 1, by omega⟩
      have h_eq : j_max.val + 1 = (sortedEndpts witness T).length - 1 := by omega
      simp [h_eq]
    rw [h_jhi_eq_last]
    have h_last_ge_one := sortedEndpts_last_ge_one witness T
    linarith

end CombArg.Scalar.Partition
