/-
Copyright (c) 2026 Xinze Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xinze Li
-/
import CombArg.Scalar.Partition.Endpoints

/-!
# `CombArg.Scalar.Partition.Pieces` — partition pieces by sorted endpoints

For `j : Fin ((endpts T).card - 1)` the `j`-th partition piece is
`Subtype.val ⁻¹' Icc (sortedEndpts[j]) (sortedEndpts[j+1])`. This
file defines `pieceLo`, `pieceHi`, `piece`, the membership iff, and
the index lookups for `(bounds tk).1` and `(bounds tk).2` in the
sorted list.
-/

namespace CombArg.Scalar.Partition

open CombArg CombArg.OneDim
open scoped Classical

variable {f : unitInterval → ℝ} {m₀ : ℝ} {N : ℕ}
variable
  (witness : ∀ t : unitInterval, f t ≥ m₀ - 1 / (N : ℝ) →
                LocalWitness unitInterval f t (1 / (4 * (N : ℝ))))

/-- Lower endpoint of the `j`-th partition piece: the `j`-th element
of the sorted endpoint list. -/
noncomputable def pieceLo (T : Finset ↥(nearCritical f m₀ N))
    (j : Fin ((endpts witness T).card - 1)) : ℝ :=
  (sortedEndpts witness T).get ⟨j.val, by
    have hL : (sortedEndpts witness T).length = (endpts witness T).card :=
      sortedEndpts_length witness T
    have h2 : 2 ≤ (endpts witness T).card := endpts_card_ge_two witness T
    have hj : j.val < (endpts witness T).card - 1 := j.isLt
    omega⟩

/-- Upper endpoint of the `j`-th partition piece. -/
noncomputable def pieceHi (T : Finset ↥(nearCritical f m₀ N))
    (j : Fin ((endpts witness T).card - 1)) : ℝ :=
  (sortedEndpts witness T).get ⟨j.val + 1, by
    have hL : (sortedEndpts witness T).length = (endpts witness T).card :=
      sortedEndpts_length witness T
    have h2 : 2 ≤ (endpts witness T).card := endpts_card_ge_two witness T
    have hj : j.val < (endpts witness T).card - 1 := j.isLt
    omega⟩

/-- The lower endpoint is strictly less than the upper endpoint
(strict monotonicity of the sorted list). -/
lemma pieceLo_lt_pieceHi (T : Finset ↥(nearCritical f m₀ N))
    (j : Fin ((endpts witness T).card - 1)) :
    pieceLo witness T j < pieceHi witness T j := by
  have h_smono : StrictMono (sortedEndpts witness T).get :=
    sortedEndpts_sortedLT witness T
  exact h_smono (Fin.mk_lt_mk.mpr (Nat.lt_succ_self j.val))

/-- The `j`-th partition piece, as a subset of `unitInterval`:
preimage of the closed interval between consecutive sorted endpoints. -/
noncomputable def piece (T : Finset ↥(nearCritical f m₀ N))
    (j : Fin ((endpts witness T).card - 1)) : Set unitInterval :=
  Subtype.val ⁻¹' Set.Icc (pieceLo witness T j) (pieceHi witness T j)

/-- Membership in `piece T j`: a point `t : unitInterval` lies in the
`j`-th piece iff `t.val` is in the closed interval between the
consecutive sorted endpoints. -/
@[simp] lemma mem_piece_iff (T : Finset ↥(nearCritical f m₀ N))
    (j : Fin ((endpts witness T).card - 1)) (t : unitInterval) :
    t ∈ piece witness T j ↔
    pieceLo witness T j ≤ t.val ∧ t.val ≤ pieceHi witness T j := by
  unfold piece
  rw [Set.mem_preimage, Set.mem_Icc]

/-- `(bounds tk).1`, being in the endpoint Finset, is one of the
`sortedEndpts` entries: there is some index `i` into the sorted list
with `sortedEndpts[i] = (bounds tk).1`. -/
lemma exists_index_of_bounds_left
    {T : Finset ↥(nearCritical f m₀ N)} {tk : ↥(nearCritical f m₀ N)}
    (htk : tk ∈ T) :
    ∃ i : Fin (sortedEndpts witness T).length,
      (sortedEndpts witness T).get i = (bounds witness tk).1 := by
  have h_mem : (bounds witness tk).1 ∈ sortedEndpts witness T :=
    (mem_sortedEndpts_iff witness T _).mpr (bounds_left_mem_endpts witness htk)
  exact List.mem_iff_get.mp h_mem

/-- Same for `(bounds tk).2`. -/
lemma exists_index_of_bounds_right
    {T : Finset ↥(nearCritical f m₀ N)} {tk : ↥(nearCritical f m₀ N)}
    (htk : tk ∈ T) :
    ∃ i : Fin (sortedEndpts witness T).length,
      (sortedEndpts witness T).get i = (bounds witness tk).2 := by
  have h_mem : (bounds witness tk).2 ∈ sortedEndpts witness T :=
    (mem_sortedEndpts_iff witness T _).mpr (bounds_right_mem_endpts witness htk)
  exact List.mem_iff_get.mp h_mem

end CombArg.Scalar.Partition
