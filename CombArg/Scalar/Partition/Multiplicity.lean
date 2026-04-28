/-
Copyright (c) 2026 Xinze Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xinze Li
-/
import CombArg.Scalar.Partition.Pieces

/-!
# `CombArg.Scalar.Partition.Multiplicity` — multiplicity ≤ 2 of pieces

Two pieces with index gap ≥ 2 are disjoint: from `t ∈ piece j₁` and
`t ∈ piece j₃` with `j₁ + 2 ≤ j₃`, the closed intervals `Icc lo₁ hi₁`
and `Icc lo₃ hi₃` would have to intersect, forcing
`sortedEndpts[j₃] ≤ sortedEndpts[j₁ + 1]`, hence `j₃ ≤ j₁ + 1` by strict
monotonicity --- contradicting the gap.
-/

namespace CombArg.Scalar.Partition

open CombArg CombArg.OneDim
open scoped Classical

variable {f : unitInterval → ℝ} {m₀ : ℝ} {N : ℕ}
variable
  (witness : ∀ t : unitInterval, f t ≥ m₀ - 1 / (N : ℝ) →
                LocalWitness unitInterval f t (1 / (4 * (N : ℝ))))

/-- Two pieces at index gap `≥ 2` cannot share a point. -/
lemma piece_disjoint_of_gap_ge_two
    {T : Finset ↥(nearCritical f m₀ N)}
    {j1 j3 : Fin ((endpts witness T).card - 1)}
    (h_gap : j1.val + 2 ≤ j3.val)
    {t : unitInterval}
    (h1 : t ∈ piece witness T j1)
    (h3 : t ∈ piece witness T j3) : False := by
  rw [mem_piece_iff] at h1 h3
  have h_smono : StrictMono (sortedEndpts witness T).get :=
    sortedEndpts_sortedLT witness T
  have hL : (sortedEndpts witness T).length = (endpts witness T).card :=
    sortedEndpts_length witness T
  have h2 : 2 ≤ (endpts witness T).card := endpts_card_ge_two witness T
  have hj1 : j1.val < (endpts witness T).card - 1 := j1.isLt
  have hj3 : j3.val < (endpts witness T).card - 1 := j3.isLt
  have h_j1plus_lt_len : j1.val + 1 < (sortedEndpts witness T).length := by omega
  have h_j3_lt_len : j3.val < (sortedEndpts witness T).length := by omega
  have hHi_eq :
      pieceHi witness T j1 =
        (sortedEndpts witness T).get ⟨j1.val + 1, h_j1plus_lt_len⟩ := rfl
  have hLo_eq :
      pieceLo witness T j3 =
        (sortedEndpts witness T).get ⟨j3.val, h_j3_lt_len⟩ := rfl
  have h_lo3_le_hi1 :
      (sortedEndpts witness T).get ⟨j3.val, h_j3_lt_len⟩
        ≤ (sortedEndpts witness T).get ⟨j1.val + 1, h_j1plus_lt_len⟩ := by
    rw [← hLo_eq, ← hHi_eq]; linarith [h1.2, h3.1]
  have h_idx_le : j3.val ≤ j1.val + 1 := h_smono.le_iff_le.mp h_lo3_le_hi1
  omega

/-- **Multiplicity ≤ 2**: every `t : unitInterval` lies in at most two
partition pieces. Proof: if three distinct pieces `j₁, j₂, j₃` all
contained `t`, sorting them by index yields a pair at gap `≥ 2`, which
`piece_disjoint_of_gap_ge_two` forbids. -/
lemma piece_multiplicity_le_two
    (T : Finset ↥(nearCritical f m₀ N)) (t : unitInterval) :
    (Finset.univ.filter
      (fun j : Fin ((endpts witness T).card - 1) =>
        t ∈ piece witness T j)).card ≤ 2 := by
  by_contra h_not
  have h_gt : 2 < (Finset.univ.filter
      (fun j : Fin ((endpts witness T).card - 1) =>
        t ∈ piece witness T j)).card := by omega
  obtain ⟨j1, j2, j3, hj1, hj2, hj3, h12, h13, h23⟩ :=
    Finset.two_lt_card_iff.mp h_gt
  have hp1 : t ∈ piece witness T j1 := (Finset.mem_filter.mp hj1).2
  have hp2 : t ∈ piece witness T j2 := (Finset.mem_filter.mp hj2).2
  have hp3 : t ∈ piece witness T j3 := (Finset.mem_filter.mp hj3).2
  rcases lt_trichotomy j1.val j2.val with hl1 | he1 | hg1
  · rcases lt_trichotomy j2.val j3.val with hl2 | he2 | hg2
    · -- j1 < j2 < j3 ⇒ j1.val + 2 ≤ j3.val.
      exact piece_disjoint_of_gap_ge_two witness (by omega) hp1 hp3
    · exact h23 (Fin.ext he2)
    · rcases lt_trichotomy j1.val j3.val with hl3 | he3 | hg3
      · -- j1 < j3 < j2 ⇒ j1.val + 2 ≤ j2.val.
        exact piece_disjoint_of_gap_ge_two witness (by omega) hp1 hp2
      · exact h13 (Fin.ext he3)
      · -- j3 < j1 < j2 ⇒ j3.val + 2 ≤ j2.val.
        exact piece_disjoint_of_gap_ge_two witness (by omega) hp3 hp2
  · exact h12 (Fin.ext he1)
  · rcases lt_trichotomy j1.val j3.val with hl3 | he3 | hg3
    · -- j2 < j1 < j3 ⇒ j2.val + 2 ≤ j3.val.
      exact piece_disjoint_of_gap_ge_two witness (by omega) hp2 hp3
    · exact h13 (Fin.ext he3)
    · rcases lt_trichotomy j2.val j3.val with hl2 | he2 | hg2
      · -- j2 < j3 < j1 ⇒ j2.val + 2 ≤ j1.val.
        exact piece_disjoint_of_gap_ge_two witness (by omega) hp2 hp1
      · exact h23 (Fin.ext he2)
      · -- j3 < j2 < j1 ⇒ j3.val + 2 ≤ j1.val.
        exact piece_disjoint_of_gap_ge_two witness (by omega) hp3 hp1

end CombArg.Scalar.Partition
