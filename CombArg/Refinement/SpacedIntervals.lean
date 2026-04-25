/-
Copyright (c) 2026 Xinze Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xinze Li
-/
import CombArg.Util
import Mathlib.Topology.UnitInterval

/-!
# Skip-2 spaced open intervals on the unit interval

A purely geometric structure: a finite family of open intervals on
`unitInterval`, each specified by a center and a positive radius,
subject to the spacing condition
`c_i + r_i < c_{i+2} − r_{i+2}` for every valid `i`.

From this data alone (independent of any witnesses, near-critical
set, or pairable-cover structure) one derives
* `chain_spacing` — iterated spacing at even gaps,
* `disjoint_of_even_gap` — open intervals at even gap are disjoint,
* `closure_disjoint_of_even_gap` — their closures are disjoint,
* `not_three_overlap` — no point lies in three of the interval
  closures at distinct sorted indices (parity rescue, combining
  even-gap disjointness with
  `CombArg.exists_even_gap_of_three`).

The `InitialCover` structure in `CombArg/Refinement/InitialCover.lean`
carries one of these as the geometric part of its data, and its
disjointness lemmas are derived by delegating to this file.
-/

namespace CombArg.Refinement

/-- The open interval of radius `r` around `c : unitInterval`, as
a subset of `unitInterval` via the subtype preimage. Used as the
canonical shape of pieces in `SkippedSpacedIntervals` and
`InitialCover`. -/
def openInterval (c : unitInterval) (r : ℝ) : Set unitInterval :=
  Subtype.val ⁻¹' Set.Ioo (c.val - r) (c.val + r)

/-- A finite family of open intervals on `unitInterval`, indexed by
`Fin n`, with positive radii and the skip-2 spacing condition. -/
structure SkippedSpacedIntervals where
  /-- Number of intervals. -/
  n : ℕ
  /-- Center of the `i`-th interval. -/
  intervalCenter : Fin n → unitInterval
  /-- Radius of the `i`-th interval. -/
  radius : Fin n → ℝ
  /-- Each radius is strictly positive. -/
  radius_pos : ∀ i, 0 < radius i
  /-- Skip-2 spacing: consecutive-by-two indices have strictly
  separated closures. -/
  two_fold_spacing : ∀ (i : Fin n) (h : i.val + 2 < n),
    (intervalCenter i).val + radius i <
      (intervalCenter ⟨i.val + 2, h⟩).val -
        radius ⟨i.val + 2, h⟩

namespace SkippedSpacedIntervals

/-- The `i`-th open interval `I_i` as a subset of `unitInterval`. -/
def I (sp : SkippedSpacedIntervals) (i : Fin sp.n) : Set unitInterval :=
  openInterval (sp.intervalCenter i) (sp.radius i)

/-- **Chain spacing**: iterated `two_fold_spacing` at gap `2(m+1)`. -/
lemma chain_spacing (sp : SkippedSpacedIntervals) (i : Fin sp.n) :
    ∀ (m : ℕ) (j : Fin sp.n), j.val = i.val + 2 * (m + 1) →
      (sp.intervalCenter i).val + sp.radius i <
        (sp.intervalCenter j).val - sp.radius j := by
  intro m
  induction m with
  | zero =>
    intro j h_gap
    have h_bound : i.val + 2 < sp.n := by
      have : j.val < sp.n := j.isLt
      omega
    have h_fin_eq : j = (⟨i.val + 2, h_bound⟩ : Fin sp.n) := by
      apply Fin.ext
      simp [h_gap]
    rw [h_fin_eq]
    exact sp.two_fold_spacing i h_bound
  | succ k ih =>
    intro j h_gap
    have h_mid_bound : i.val + 2 * (k + 1) < sp.n := by
      have : j.val < sp.n := j.isLt
      omega
    let j_mid : Fin sp.n := ⟨i.val + 2 * (k + 1), h_mid_bound⟩
    have h_j_mid : j_mid.val = i.val + 2 * (k + 1) := rfl
    have h_ih := ih j_mid h_j_mid
    have h_plus_bound : j_mid.val + 2 < sp.n := by
      show i.val + 2 * (k + 1) + 2 < sp.n
      have : j.val < sp.n := j.isLt
      omega
    have h_spacing_mid := sp.two_fold_spacing j_mid h_plus_bound
    have hr_pos : 0 < sp.radius j_mid := sp.radius_pos j_mid
    have h_fin_eq : j = (⟨j_mid.val + 2, h_plus_bound⟩ : Fin sp.n) := by
      apply Fin.ext
      show j.val = j_mid.val + 2
      rw [h_j_mid, h_gap]
      ring
    rw [h_fin_eq]
    linarith [h_ih, h_spacing_mid, hr_pos]

/-- **Even-gap disjointness (open intervals)**. -/
lemma disjoint_of_even_gap (sp : SkippedSpacedIntervals)
    (i j : Fin sp.n) (m : ℕ) (h_gap : j.val = i.val + 2 * (m + 1)) :
    Disjoint (sp.I i) (sp.I j) := by
  have h_strict := sp.chain_spacing i m j h_gap
  rw [Set.disjoint_iff]
  intro t ht
  simp only [I, openInterval, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ioo] at ht
  obtain ⟨⟨_, h1⟩, ⟨h2, _⟩⟩ := ht
  linarith

/-- **Even-gap disjointness of closures**. -/
lemma closure_disjoint_of_even_gap (sp : SkippedSpacedIntervals)
    (i j : Fin sp.n) (m : ℕ) (h_gap : j.val = i.val + 2 * (m + 1)) :
    Disjoint (closure (sp.I i)) (closure (sp.I j)) := by
  have h_strict := sp.chain_spacing i m j h_gap
  rw [Set.disjoint_iff]
  intro t ⟨ht_i, ht_j⟩
  have h_cl : ∀ x : Fin sp.n, closure (sp.I x) ⊆
      Subtype.val ⁻¹'
        Set.Icc ((sp.intervalCenter x).val - sp.radius x)
                ((sp.intervalCenter x).val + sp.radius x) := by
    intro x
    apply closure_minimal
    · intro s hs
      simp only [I, openInterval, Set.mem_preimage, Set.mem_Ioo] at hs
      simp only [Set.mem_preimage, Set.mem_Icc]
      exact ⟨le_of_lt hs.1, le_of_lt hs.2⟩
    · exact isClosed_Icc.preimage continuous_subtype_val
  have hi_bound := h_cl i ht_i
  have hj_bound := h_cl j ht_j
  simp only [Set.mem_preimage, Set.mem_Icc] at hi_bound hj_bound
  linarith [hi_bound.2, hj_bound.1]

/-- **Parity rescue**: no point lies in three interval closures at
distinct sorted indices. Combines `closure_disjoint_of_even_gap`
with `CombArg.exists_even_gap_of_three`. -/
lemma not_three_overlap (sp : SkippedSpacedIntervals)
    (a b c : Fin sp.n) (hab : a.val < b.val) (hbc : b.val < c.val)
    (t : unitInterval)
    (ha : t ∈ closure (sp.I a)) (hb : t ∈ closure (sp.I b))
    (hc : t ∈ closure (sp.I c)) :
    False := by
  rcases CombArg.exists_even_gap_of_three hab hbc with
    ⟨hge, hmod⟩ | ⟨hge, hmod⟩ | ⟨hge, hmod⟩
  · exact (Set.disjoint_iff.mp
      (sp.closure_disjoint_of_even_gap a c ((c.val - a.val) / 2 - 1)
        (by omega))) ⟨ha, hc⟩
  · exact (Set.disjoint_iff.mp
      (sp.closure_disjoint_of_even_gap a b ((b.val - a.val) / 2 - 1)
        (by omega))) ⟨ha, hb⟩
  · exact (Set.disjoint_iff.mp
      (sp.closure_disjoint_of_even_gap b c ((c.val - b.val) / 2 - 1)
        (by omega))) ⟨hb, hc⟩

/-- **Parity rescue, unordered variant**: no point lies in three
interval closures at three distinct indices (regardless of how
the indices are sorted). Sorts the three `.val`s by trichotomy
and delegates to `not_three_overlap`. -/
lemma not_three_overlap_any_order (sp : SkippedSpacedIntervals)
    (a b c : Fin sp.n)
    (hab : a.val ≠ b.val) (hac : a.val ≠ c.val) (hbc : b.val ≠ c.val)
    (t : unitInterval)
    (ha : t ∈ closure (sp.I a)) (hb : t ∈ closure (sp.I b))
    (hc : t ∈ closure (sp.I c)) :
    False := by
  rcases lt_trichotomy a.val b.val with h12 | h12 | h12
  · rcases lt_trichotomy b.val c.val with h23 | h23 | h23
    · exact sp.not_three_overlap a b c h12 h23 t ha hb hc
    · exact hbc h23
    · rcases lt_trichotomy a.val c.val with h13 | h13 | h13
      · exact sp.not_three_overlap a c b h13 h23 t ha hc hb
      · exact hac h13
      · exact sp.not_three_overlap c a b h13 h12 t hc ha hb
  · exact hab h12
  · rcases lt_trichotomy a.val c.val with h13 | h13 | h13
    · exact sp.not_three_overlap b a c h12 h13 t hb ha hc
    · exact hac h13
    · rcases lt_trichotomy b.val c.val with h23 | h23 | h23
      · exact sp.not_three_overlap b c a h23 h13 t hb hc ha
      · exact hbc h23
      · exact sp.not_three_overlap c b a h23 h12 t hc hb ha

end SkippedSpacedIntervals

end CombArg.Refinement
