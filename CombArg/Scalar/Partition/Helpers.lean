/-
Copyright (c) 2026 Xinze Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xinze Li
-/
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.Compact

/-!
# `CombArg.Scalar.Partition.Helpers` — generic topology helpers

Two helpers used by the partition-route construction, both
independent of the witness data:

* `mem_closure_val_preimage_Ioo` — for `a < 1`, `0 < b`, `a < b`,
  any `t : unitInterval` with `t.val ∈ Icc a b` lies in the closure
  (in `unitInterval`) of `Subtype.val ⁻¹' Ioo a b`. Reduces via the
  subtype-embedding closure formula to `closure_Ioo` in `ℝ`.

* `exists_open_Ioo_subset_of_open` — an open set in `unitInterval`
  containing `t` admits an open `Ioo (a, b)` around `t.val` whose
  preimage is contained in the set.
-/

namespace CombArg.Scalar.Partition

/-- For an open set `U` in `unitInterval` containing `t`, there exist
real bounds `a < t.val < b` such that the preimage of `Ioo a b` under
`Subtype.val` is contained in `U`. Standard consequence of the
subspace topology: an open ball in `unitInterval` is the preimage of
an open interval in `ℝ`. -/
lemma exists_open_Ioo_subset_of_open
    {U : Set unitInterval} (hU : IsOpen U) {t : unitInterval} (ht : t ∈ U) :
    ∃ a b : ℝ, a < t.val ∧ t.val < b ∧
      Subtype.val ⁻¹' Set.Ioo a b ⊆ U := by
  rw [Metric.isOpen_iff] at hU
  obtain ⟨ε, hε_pos, hε⟩ := hU t ht
  refine ⟨t.val - ε, t.val + ε, by linarith, by linarith, ?_⟩
  intro s hs
  apply hε
  rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq]
  rw [Set.mem_preimage, Set.mem_Ioo] at hs
  rw [abs_lt]
  refine ⟨?_, ?_⟩ <;> linarith

/-- If `a < 1`, `0 < b`, `a < b`, then any `t : unitInterval` with
`t.val ∈ Icc a b` is in the closure of `val⁻¹(Ioo a b)`. Reduces via
the subtype embedding to the standard `closure_Ioo` in `ℝ`: the
clamped sub-interval `Ioo (max a 0) (min b 1)` is a subset of
`Ioo a b ∩ unitInterval`, its closure equals `Icc (max a 0) (min b 1)`,
and `t.val` lies in that closed interval. -/
lemma mem_closure_val_preimage_Ioo
    {a b : ℝ} (h_lt_one : a < 1) (h_pos : 0 < b) (hab : a < b)
    {t : unitInterval} (ht : t.val ∈ Set.Icc a b) :
    t ∈ closure (Subtype.val ⁻¹' Set.Ioo a b : Set unitInterval) := by
  rw [Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image,
      Set.image_preimage_eq_inter_range, Subtype.range_val]
  show t.val ∈ closure (Set.Ioo a b ∩ unitInterval)
  have h_max_lt_min : max a 0 < min b 1 := by
    rcases lt_or_ge a 0 with h_a_neg | h_a_nn
    · rw [max_eq_right h_a_neg.le]; exact lt_min h_pos one_pos
    · rw [max_eq_left h_a_nn]; exact lt_min hab h_lt_one
  have h_subset :
      Set.Ioo (max a 0) (min b 1) ⊆ Set.Ioo a b ∩ unitInterval := by
    intro x ⟨hx_lo, hx_hi⟩
    refine ⟨⟨lt_of_le_of_lt (le_max_left _ _) hx_lo,
            lt_of_lt_of_le hx_hi (min_le_left _ _)⟩,
           le_of_lt (lt_of_le_of_lt (le_max_right _ _) hx_lo),
           le_of_lt (lt_of_lt_of_le hx_hi (min_le_right _ _))⟩
  have h_t_in_clamped : t.val ∈ Set.Icc (max a 0) (min b 1) :=
    ⟨max_le ht.1 t.2.1, le_min ht.2 t.2.2⟩
  rw [← closure_Ioo (ne_of_lt h_max_lt_min)] at h_t_in_clamped
  exact closure_mono h_subset h_t_in_clamped

end CombArg.Scalar.Partition
