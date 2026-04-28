/-
Copyright (c) 2026 Xinze Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xinze Li
-/
import CombArg.Cover
import CombArg.Witness
import CombArg.OneDim.InitialCover
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Sort
import Mathlib.Order.Bounds.Basic

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
   finite open cover.
2. Inside each witness neighborhood, extract an open interval
   `(a_i, b_i)` containing the witness center (subspace topology).
   The `(a_i, b_i)` cover `nearCritical`.
3. By `IsCompact.elim_finite_subcover`, reduce to a finite indexing
   `T : Finset (nearCritical f m₀ N)`.
4. Form the endpoint Finset `E : Finset ℝ` containing `0`, `1`, and
   all `a_i, b_i` for `i ∈ T`. Sort to a list `[e₀, e₁, …, e_M]`.
5. The pieces are `q_j := Subtype.val ⁻¹' Icc e_j e_{j+1}` for
   `j : Fin (M-1)`. By construction, on each open interior
   `(e_j, e_{j+1})` the indicator "is in `(a_i, b_i)`" is constant in
   `i` --- because no `a_i` or `b_i` lies strictly between
   consecutive sorted endpoints --- so each piece is contained in
   `Subtype.val ⁻¹' Icc a_i b_i = closure (Subtype.val ⁻¹' Ioo a_i b_i)`
   for some `i ∈ T`.
6. **Multiplicity ≤ 2**: consecutive pieces `q_j, q_{j+1}` share
   only the boundary point `e_{j+1}`; non-consecutive pieces are
   disjoint. So every `t ∈ unitInterval` belongs to at most two
   pieces.
7. **Coverage of `nearCritical`**: the pieces partition
   `unitInterval` (up to boundary identifications), so
   `nearCritical ⊆ ⋃ q_j`.
8. **Saving bound**: on each `q_j`, the witness `i_j` satisfies
   `f − E_{i_j} ≥ 1/(4N)` on `Subtype.val ⁻¹' Ioo a_{i_j} b_{i_j}`;
   continuity of `f − E_{i_j}` lifts the inequality to the closure
   `Subtype.val ⁻¹' Icc a_{i_j} b_{i_j} ⊇ q_j`.

The result is a `FiniteCoverWithWitnesses unitInterval f m₀ (1/N) (1/(4N))`
with the same external interface as `OneDim.exists_refinement`.
-/

namespace CombArg.Scalar

open CombArg CombArg.OneDim
open scoped Classical

variable {f : unitInterval → ℝ} {m₀ : ℝ} {N : ℕ}

/-! ## Helpers -/

/-- If `a < 1`, `0 < b`, `a < b`, then any `t : unitInterval` with
`t.val ∈ Icc a b` is in the closure of `val⁻¹(Ioo a b)`. Reduces via
the subtype embedding to the standard `closure_Ioo` in `ℝ`: the
clamped sub-interval `Ioo (max a 0) (min b 1)` is a subset of
`Ioo a b ∩ unitInterval`, its closure equals `Icc (max a 0) (min b 1)`,
and `t.val` lies in that closed interval. -/
private lemma mem_closure_val_preimage_Ioo
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

/-- For an open set `U` in `unitInterval` containing `t`, there exist
real bounds `a < t.val < b` such that the preimage of `Ioo a b` under
`Subtype.val` is contained in `U`. Standard consequence of the
subspace topology: an open ball in `unitInterval` is the preimage of
an open interval in `ℝ`. -/
private lemma exists_open_Ioo_subset_of_open
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

/-! ## Per-witness interval data

For each near-critical `tk`, the witness gives an open neighborhood;
inside it we extract an open interval `Ioo (boundsLeft tk) (boundsRight tk)`
containing `tk.val.val` whose preimage under `Subtype.val` lies in
the neighborhood. The `Classical.choose` extraction is wrapped into
`noncomputable def`s with the key spec exposed as lemmas, to keep
the main proof's binder structure tractable. -/

variable
  (witness : ∀ t : unitInterval, f t ≥ m₀ - 1 / (N : ℝ) →
                LocalWitness unitInterval f t (1 / (4 * (N : ℝ))))

/-- The bundled `(a, b)` extracted from the open neighborhood of the
witness at a near-critical point `tk`. -/
private noncomputable def bounds (tk : ↥(nearCritical f m₀ N)) : ℝ × ℝ :=
  let h := exists_open_Ioo_subset_of_open
            (witness tk.val tk.property).isOpen_neighborhood
            (witness tk.val tk.property).t_mem
  ⟨h.choose, h.choose_spec.choose⟩

/-- Defining property of `bounds`: `tk.val.val` lies strictly inside
the interval, and the preimage of the open interval is contained in
the witness neighborhood. -/
private lemma bounds_spec (tk : ↥(nearCritical f m₀ N)) :
    (bounds witness tk).1 < tk.val.val ∧ tk.val.val < (bounds witness tk).2 ∧
    Subtype.val ⁻¹' Set.Ioo (bounds witness tk).1 (bounds witness tk).2
      ⊆ (witness tk.val tk.property).neighborhood :=
  let h := exists_open_Ioo_subset_of_open
            (witness tk.val tk.property).isOpen_neighborhood
            (witness tk.val tk.property).t_mem
  h.choose_spec.choose_spec

/-- The `Ioo`-preimage open cover at a near-critical point. -/
private noncomputable def coverIvl (tk : ↥(nearCritical f m₀ N)) :
    Set unitInterval :=
  Subtype.val ⁻¹' Set.Ioo (bounds witness tk).1 (bounds witness tk).2

/-- `coverIvl` is open. -/
private lemma isOpen_coverIvl (tk : ↥(nearCritical f m₀ N)) :
    IsOpen (coverIvl witness tk) :=
  isOpen_Ioo.preimage continuous_subtype_val

/-- Each near-critical point lies in its own `coverIvl`. -/
private lemma mem_coverIvl_self (tk : ↥(nearCritical f m₀ N)) :
    tk.val ∈ coverIvl witness tk := by
  show tk.val.val ∈ Set.Ioo (bounds witness tk).1 (bounds witness tk).2
  have h := bounds_spec witness tk
  exact ⟨h.1, h.2.1⟩

/-- The family `{coverIvl tk}` covers `nearCritical`. -/
private lemma coverIvl_covers_nearCritical :
    nearCritical f m₀ N ⊆ ⋃ tk : ↥(nearCritical f m₀ N), coverIvl witness tk := by
  intro t ht
  exact Set.mem_iUnion.mpr ⟨⟨t, ht⟩, mem_coverIvl_self witness ⟨t, ht⟩⟩

/-! ## Endpoint Finset and sorted partition

From a finite subcover indexed by `T : Finset (↥(nearCritical f m₀ N))`,
collect all interval endpoints `{0, 1, (bounds tk).1, (bounds tk).2 : tk ∈ T}`
into a Finset `endpts T` of reals, sort it, and read off the partition
pieces between consecutive sorted endpoints. -/

/-- Endpoints of the witness intervals together with `0` and `1`. -/
private noncomputable def endpts (T : Finset ↥(nearCritical f m₀ N)) :
    Finset ℝ :=
  insert (0 : ℝ) (insert (1 : ℝ)
    (T.image (fun tk => (bounds witness tk).1)
      ∪ T.image (fun tk => (bounds witness tk).2)))

/-- `endpts T` contains `0` and `1`, hence has at least two elements. -/
private lemma endpts_card_ge_two (T : Finset ↥(nearCritical f m₀ N)) :
    2 ≤ (endpts witness T).card :=
  Finset.one_lt_card.mpr
    ⟨0, Finset.mem_insert_self _ _,
     1, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),
     by norm_num⟩

/-- The sorted list of endpoints, in non-decreasing order (using the
default `(· ≤ ·)` relation on `ℝ`). -/
private noncomputable def sortedEndpts (T : Finset ↥(nearCritical f m₀ N)) :
    List ℝ :=
  (endpts witness T).sort

/-- The sorted endpoint list has length equal to the endpoint Finset's
cardinality. -/
private lemma sortedEndpts_length (T : Finset ↥(nearCritical f m₀ N)) :
    (sortedEndpts witness T).length = (endpts witness T).card :=
  Finset.length_sort _

/-- The sorted endpoint list is strictly increasing. (`Finset.sort`
of a Finset --- which has no duplicates --- ascending is strict.) -/
private lemma sortedEndpts_sortedLT (T : Finset ↥(nearCritical f m₀ N)) :
    (sortedEndpts witness T).SortedLT :=
  Finset.sortedLT_sort _

/-- The sorted endpoint list contains exactly the elements of the
endpoint Finset. -/
private lemma mem_sortedEndpts_iff (T : Finset ↥(nearCritical f m₀ N))
    (x : ℝ) : x ∈ sortedEndpts witness T ↔ x ∈ endpts witness T :=
  Finset.mem_sort _

/-- Each `(bounds tk).1` is in the endpoint Finset (and hence in the
sorted list). -/
private lemma bounds_left_mem_endpts {T : Finset ↥(nearCritical f m₀ N)}
    {tk : ↥(nearCritical f m₀ N)} (htk : tk ∈ T) :
    (bounds witness tk).1 ∈ endpts witness T := by
  unfold endpts
  refine Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ?_)
  exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨tk, htk, rfl⟩)

/-- Each `(bounds tk).2` is in the endpoint Finset. -/
private lemma bounds_right_mem_endpts {T : Finset ↥(nearCritical f m₀ N)}
    {tk : ↥(nearCritical f m₀ N)} (htk : tk ∈ T) :
    (bounds witness tk).2 ∈ endpts witness T := by
  unfold endpts
  refine Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ?_)
  exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨tk, htk, rfl⟩)

/-! ## Pieces between consecutive sorted endpoints -/

/-- Lower endpoint of the `j`-th partition piece: the `j`-th element
of the sorted endpoint list. -/
private noncomputable def pieceLo (T : Finset ↥(nearCritical f m₀ N))
    (j : Fin ((endpts witness T).card - 1)) : ℝ :=
  (sortedEndpts witness T).get ⟨j.val, by
    have hL : (sortedEndpts witness T).length = (endpts witness T).card :=
      sortedEndpts_length witness T
    have h2 : 2 ≤ (endpts witness T).card := endpts_card_ge_two witness T
    have hj : j.val < (endpts witness T).card - 1 := j.isLt
    omega⟩

/-- Upper endpoint of the `j`-th partition piece. -/
private noncomputable def pieceHi (T : Finset ↥(nearCritical f m₀ N))
    (j : Fin ((endpts witness T).card - 1)) : ℝ :=
  (sortedEndpts witness T).get ⟨j.val + 1, by
    have hL : (sortedEndpts witness T).length = (endpts witness T).card :=
      sortedEndpts_length witness T
    have h2 : 2 ≤ (endpts witness T).card := endpts_card_ge_two witness T
    have hj : j.val < (endpts witness T).card - 1 := j.isLt
    omega⟩

/-- The lower endpoint is strictly less than the upper endpoint
(strict monotonicity of the sorted list). -/
private lemma pieceLo_lt_pieceHi (T : Finset ↥(nearCritical f m₀ N))
    (j : Fin ((endpts witness T).card - 1)) :
    pieceLo witness T j < pieceHi witness T j := by
  have h_smono : StrictMono (sortedEndpts witness T).get :=
    sortedEndpts_sortedLT witness T
  exact h_smono (Fin.mk_lt_mk.mpr (Nat.lt_succ_self j.val))

/-- The `j`-th partition piece, as a subset of `unitInterval`:
preimage of the closed interval between consecutive sorted endpoints. -/
private noncomputable def piece (T : Finset ↥(nearCritical f m₀ N))
    (j : Fin ((endpts witness T).card - 1)) : Set unitInterval :=
  Subtype.val ⁻¹' Set.Icc (pieceLo witness T j) (pieceHi witness T j)

/-- Membership in `piece T j`: a point `t : unitInterval` lies in the
`j`-th piece iff `t.val` is in the closed interval between the
consecutive sorted endpoints. -/
@[simp] private lemma mem_piece_iff (T : Finset ↥(nearCritical f m₀ N))
    (j : Fin ((endpts witness T).card - 1)) (t : unitInterval) :
    t ∈ piece witness T j ↔
    pieceLo witness T j ≤ t.val ∧ t.val ≤ pieceHi witness T j := by
  unfold piece
  rw [Set.mem_preimage, Set.mem_Icc]

/-- `(bounds tk).1`, being in the endpoint Finset, is one of the
`sortedEndpts` entries: there is some index `i` into the sorted list
with `sortedEndpts[i] = (bounds tk).1`. -/
private lemma exists_index_of_bounds_left
    {T : Finset ↥(nearCritical f m₀ N)} {tk : ↥(nearCritical f m₀ N)}
    (htk : tk ∈ T) :
    ∃ i : Fin (sortedEndpts witness T).length,
      (sortedEndpts witness T).get i = (bounds witness tk).1 := by
  have h_mem : (bounds witness tk).1 ∈ sortedEndpts witness T :=
    (mem_sortedEndpts_iff witness T _).mpr (bounds_left_mem_endpts witness htk)
  exact List.mem_iff_get.mp h_mem

/-- Same for `(bounds tk).2`. -/
private lemma exists_index_of_bounds_right
    {T : Finset ↥(nearCritical f m₀ N)} {tk : ↥(nearCritical f m₀ N)}
    (htk : tk ∈ T) :
    ∃ i : Fin (sortedEndpts witness T).length,
      (sortedEndpts witness T).get i = (bounds witness tk).2 := by
  have h_mem : (bounds witness tk).2 ∈ sortedEndpts witness T :=
    (mem_sortedEndpts_iff witness T _).mpr (bounds_right_mem_endpts witness htk)
  exact List.mem_iff_get.mp h_mem

/-! ## Witness selection per piece

For each partition piece `q_j` whose interior intersects `nearCritical`,
some witness in `T` covers the entire closed piece. The argument: a
point `t ∈ q_j ∩ nearCritical` lies in some `coverIvl tk = val⁻¹(Ioo a_{tk} b_{tk})`,
so `a_{tk} < t.val < b_{tk}`. Both `a_{tk}` and `b_{tk}` are in the
sorted endpoint list (no other endpoint can lie strictly between
`pieceLo j` and `pieceHi j`, since these are consecutive sorted), so
`a_{tk} ≤ pieceLo j` and `pieceHi j ≤ b_{tk}`. Hence
`q_j ⊆ val⁻¹(Icc a_{tk} b_{tk})`. -/

/-- The witness selection lemma. -/
private lemma exists_witness_for_piece
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

/-! ## Multiplicity ≤ 2

Two pieces with index gap ≥ 2 are disjoint: from `t ∈ piece j₁` and
`t ∈ piece j₃` with `j₁ + 2 ≤ j₃`, the closed intervals `Icc lo₁ hi₁`
and `Icc lo₃ hi₃` would have to intersect, forcing
`sortedEndpts[j₃] ≤ sortedEndpts[j₁ + 1]`, hence `j₃ ≤ j₁ + 1` by strict
monotonicity --- contradicting the gap. -/

/-- Two pieces at index gap `≥ 2` cannot share a point. -/
private lemma piece_disjoint_of_gap_ge_two
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
private lemma piece_multiplicity_le_two
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

/-! ## Coverage of `unitInterval` (and hence `nearCritical`)

The pieces `{piece j : j ∈ Fin (M-1)}` cover the entire `unitInterval`,
hence in particular cover `nearCritical`. The argument: for any
`t : unitInterval`, take `j_max` to be the largest index in
`Fin (M-1)` with `pieceLo j_max ≤ t.val`. Such an index exists because
`pieceLo ⟨0, _⟩ = sortedEndpts[0] ≤ 0 ≤ t.val` (since `0 ∈ endpts`).
And `t.val ≤ pieceHi j_max` because either `j_max.val + 1 < M - 1`,
in which case maximality forces the next index to fail
`pieceLo ≤ t.val`; or `j_max.val = M - 2`, in which case `pieceHi j_max
= sortedEndpts[M-1] ≥ 1 ≥ t.val` (since `1 ∈ endpts`). -/

/-- The smallest sorted endpoint is `≤ 0`. -/
private lemma sortedEndpts_first_le_zero
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
private lemma sortedEndpts_last_ge_one
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
private lemma exists_piece_containing
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

/-! ## Assembled output

Only those `Fin ((endpts T).card - 1)` indices whose corresponding
piece intersects `nearCritical` are wrapped into the
`FiniteCoverWithWitnesses` cover. The subtype-indexed cover has no
empty pieces, no conditional witness assignment, and each piece
inherits its multiplicity bound directly from
`piece_multiplicity_le_two`.

A subtype `coveredIndex T` selects exactly the NC-meeting pieces.
For each such piece, the witness selection lemma
`exists_witness_for_piece` gives a covering witness whose
neighborhood contains the piece's open interior; saving extends to
the closed piece by `mem_closure_val_preimage_Ioo` plus
`IsClosed.closure_subset_iff`. -/

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

/-- Saving bound on the piece corresponding to a covered index. -/
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

/-- Multiplicity bound on the covered-index pieces. -/
private lemma coveredIndex_twoFold
    (T : Finset ↥(nearCritical f m₀ N)) (t : unitInterval) :
    (Finset.univ.filter
      (fun jh : coveredIndex witness T =>
        t ∈ piece witness T jh.val)).card ≤ 2 := by
  -- Inject covered-index pieces into the underlying Fin pieces via
  -- `Subtype.val`; cardinality is preserved by injectivity, and the
  -- image is a subset of the multiplicity-le-two filter.
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
   non-consecutive are disjoint). -/
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
