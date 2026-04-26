/-
Copyright (c) 2026 Xinze Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xinze Li
-/
import CombArg.OneDim.InitialCover
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Step 1 — Initial cover construction

`exists_initialCover` — from the witness hypothesis, build an
`InitialCover` via a grid + Lebesgue-number construction. Single lemma
of ~200 lines; the proof is dense combinatorial bookkeeping that
benefits from staying in one place.
-/

namespace CombArg.OneDim

open CombArg
open scoped Classical

/-! ## Auxiliary: grid rounding

A uniform `1/(M+1)`-grid on `unitInterval` always has a grid
point within distance `1/(2M)` of every `x ∈ unitInterval`.
Extracted from `exists_initialCover` so the phase of the main
construction that uses it can focus on the downstream
Lebesgue-number interaction. -/

/-- For any positive integer `M` and any grid function
`c : Fin (M + 1) → unitInterval` satisfying
`(c k).val = k.val / M`, every point of `unitInterval` is within
distance `1/(2M)` of some grid point. -/
private lemma exists_grid_round_bound
    {M : ℕ} (hM_pos : 0 < M)
    (c : Fin (M + 1) → unitInterval)
    (hc : ∀ k : Fin (M + 1), (c k).val = (k.val : ℝ) / M) :
    ∀ (x : unitInterval),
      ∃ k : Fin (M + 1), dist (c k) x ≤ (1 : ℝ) / (2 * M) := by
  have hM_real_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM_pos
  intro x
  set y : ℝ := x.val * M + 1/2 with hy_def
  have hy_nn : 0 ≤ y := by
    have := mul_nonneg x.2.1 hM_real_pos.le
    rw [hy_def]; linarith
  let k0 : ℕ := Nat.floor y
  have hk0_le_y : (k0 : ℝ) ≤ y := Nat.floor_le hy_nn
  have hy_lt : y < (k0 : ℝ) + 1 := Nat.lt_floor_add_one y
  have hk0_le_M : k0 ≤ M := by
    have hy_le : y ≤ M + 1/2 := by
      have := mul_le_mul_of_nonneg_right x.2.2 hM_real_pos.le
      rw [hy_def]; linarith
    have hk0_real : (k0 : ℝ) ≤ M + 1/2 := le_trans hk0_le_y hy_le
    by_contra h_contra
    have h_lt : M < k0 := not_le.mp h_contra
    have : (M + 1 : ℝ) ≤ k0 := by exact_mod_cast h_lt
    linarith
  have hk0_lt : k0 < M + 1 := Nat.lt_succ_of_le hk0_le_M
  refine ⟨⟨k0, hk0_lt⟩, ?_⟩
  show |((c ⟨k0, hk0_lt⟩).val : ℝ) - x.val| ≤ _
  rw [hc ⟨k0, hk0_lt⟩]
  have h_rewrite : ((k0 : ℝ) / M - x.val) = ((k0 : ℝ) - x.val * M) / M := by
    field_simp
  rw [h_rewrite, abs_div, abs_of_pos hM_real_pos]
  have h_abs_le : |(k0 : ℝ) - x.val * M| ≤ 1/2 := by
    have hy1 : (k0 : ℝ) ≤ x.val * M + 1/2 := by rw [hy_def] at hk0_le_y; exact hk0_le_y
    have hy2 : x.val * M + 1/2 < (k0 : ℝ) + 1 := by rw [hy_def] at hy_lt; exact hy_lt
    rw [abs_le]
    refine ⟨by linarith, by linarith⟩
  have h_div_le : |(k0 : ℝ) - x.val * M| / M ≤ (1/2) / M :=
    div_le_div_of_nonneg_right h_abs_le hM_real_pos.le
  have hhalf : (1 : ℝ) / 2 / M = 1 / (2 * M) := by field_simp
  linarith

/-- **Existence of an `InitialCover`** from the witness hypothesis.

Grid + Lebesgue construction using the `intervalCenter` /
`witnessCenter` split (see `docs/design-notes.md §10`):

1. Pick a witness at each near-critical point; neighborhoods form an
   open cover of `NC`.
2. Lebesgue-number lemma gives `λ > 0`: every `λ`-ball around a point
   of NC fits inside some single witness neighborhood.
3. Choose `M : ℕ` with `M > 4/λ` so that the grid `c_k := k/M`
   (for `k : Fin (M+1)`) has spacing `1/M < λ/4`.
4. Keep grid indices whose center is within `λ/4` of some NC point.
5. For each kept index `k`, apply Lebesgue at that near-NC point to
   pick `witnessCenter` whose witness neighborhood contains a full
   `λ`-ball around `c_k`.
6. Re-index the kept set as `Fin n` via `Finset.orderEmbOfFin`
   (preserves order on grid indices, hence strict mono on `.val`).
7. Take uniform `radius := 2/(3M)`. Then `r < λ/4 < λ`, so
   `I_i ⊆ ball (c_k) λ ⊆ witness neighborhood` (condition (b)); the
   grid-index gap ≥ 2 between non-adjacent kept indices gives
   `intervalCenter i+2 - intervalCenter i ≥ 2/M > 4/(3M) = 2r`
   strictly (condition (a)); and every NC point is within `1/(2M) < r`
   of its rounded grid neighbor, which is kept (coverage). -/
lemma exists_initialCover
    {f : unitInterval → ℝ} (hf : Continuous f)
    {m₀ : ℝ} (hm : m₀ = sSup (Set.range f))
    {N : ℕ} (hN : 0 < N)
    (witness : ∀ t : unitInterval, f t ≥ m₀ - 1 / (N : ℝ) →
                 LocalWitness unitInterval f t (1 / (4 * (N : ℝ)))) :
    Nonempty (InitialCover f m₀ N) := by
  -- ---------- Phase 1: Lebesgue number + grid spacing ----------
  -- NC compact, nonempty; pick a witness at each NC point.
  set NC := nearCritical f m₀ N with hNC_def
  have hNC_compact : IsCompact NC := isCompact_nearCritical hf
  have hNC_ne : NC.Nonempty := nearCritical_nonempty hf hm hN
  have w : ∀ t : NC, LocalWitness unitInterval f t.val (1 / (4 * (N : ℝ))) :=
    fun t => witness t.val t.property
  set U : NC → Set unitInterval := fun t => (w t).neighborhood
  have hU_open : ∀ t : NC, IsOpen (U t) := fun t => (w t).isOpen_neighborhood
  have hU_cover : NC ⊆ ⋃ t : NC, U t := fun x hx =>
    Set.mem_iUnion.mpr ⟨⟨x, hx⟩, (w ⟨x, hx⟩).t_mem⟩
  -- Step 2: Lebesgue number for NC + the cover.
  obtain ⟨lam, hlam_pos, hlam_spec⟩ :=
    lebesgue_number_lemma_of_metric hNC_compact hU_open hU_cover
  -- Step 3: `M : ℕ` with `M > 4/lam`, so `1/M < lam/4`.
  obtain ⟨M, hM_gt⟩ := exists_nat_gt (4 / lam)
  have hM_real_pos : (0 : ℝ) < (M : ℝ) :=
    lt_of_lt_of_le (div_pos (by norm_num : (0:ℝ) < 4) hlam_pos) hM_gt.le
  have hM_pos : 0 < M := by exact_mod_cast hM_real_pos
  have h_inv_M : (1 : ℝ) / M < lam / 4 := by
    rw [div_lt_div_iff₀ hM_real_pos (by norm_num : (0:ℝ) < 4)]
    rw [div_lt_iff₀ hlam_pos] at hM_gt
    linarith
  -- Grid `c k = k / M` lies in `unitInterval`.
  let c : Fin (M + 1) → unitInterval := fun k => ⟨k.val / M, by
    refine ⟨by positivity, ?_⟩
    rw [div_le_one hM_real_pos]
    exact_mod_cast Nat.le_of_lt_succ k.isLt⟩
  have round_bound :=
    exists_grid_round_bound hM_pos c (fun _ => rfl)
  -- ---------- Phase 2: kept grid + witness selection ----------
  let nearNC : Fin (M + 1) → Prop :=
    fun k => ∃ t : NC, dist (c k) t.val < lam / 4
  let kept : Finset (Fin (M + 1)) := Finset.univ.filter nearNC
  -- Kept is nonempty: use round_bound on any NC point.
  have h_half_lt_quarter : (1 : ℝ) / (2 * M) < lam / 4 := by
    have : (1 : ℝ) / (2 * M) < 1 / M := by
      rw [div_lt_div_iff₀ (by positivity) hM_real_pos]; linarith
    linarith
  have hkept_ne : kept.Nonempty := by
    obtain ⟨x, hx⟩ := hNC_ne
    obtain ⟨k, hk⟩ := round_bound x
    refine ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨x, hx⟩, ?_⟩⟩
    exact lt_of_le_of_lt hk h_half_lt_quarter
  -- Step 6: index kept by Fin n via orderEmbOfFin.
  set n := kept.card
  have hn_pos : 0 < n := Finset.card_pos.mpr hkept_ne
  let e : Fin n ↪o Fin (M + 1) := kept.orderEmbOfFin rfl
  have h_ei_mem : ∀ i : Fin n, e i ∈ kept := fun i =>
    kept.orderEmbOfFin_mem rfl i
  have h_near : ∀ i : Fin n, ∃ t : NC, dist (c (e i)) t.val < lam / 4 :=
    fun i => (Finset.mem_filter.mp (h_ei_mem i)).2
  let nearestNC : Fin n → NC := fun i => (h_near i).choose
  have nearestNC_dist : ∀ i, dist (c (e i)) (nearestNC i).val < lam / 4 :=
    fun i => (h_near i).choose_spec
  let wcChoice : Fin n → NC := fun i =>
    (hlam_spec (nearestNC i).val (nearestNC i).property).choose
  have wcChoice_prop : ∀ i,
      Metric.ball (nearestNC i).val lam ⊆ U (wcChoice i) :=
    fun i => (hlam_spec (nearestNC i).val (nearestNC i).property).choose_spec
  -- Step 7: radii.
  let r : ℝ := 2 / (3 * (M : ℝ))
  have hr_pos : 0 < r := by positivity
  have hr_lt_inv_M : r < 1 / M := by
    show 2 / (3 * (M : ℝ)) < 1 / M
    rw [div_lt_div_iff₀ (by positivity) hM_real_pos]
    linarith
  have hr_lt_lam4 : r < lam / 4 := lt_trans hr_lt_inv_M h_inv_M
  let intCent : Fin n → unitInterval := fun i => c (e i)
  let wc : Fin n → unitInterval := fun i => (wcChoice i).val
  -- ---------- Phase 3: assemble structure + verify invariants ----------
  refine ⟨{
    n := n
    n_pos := hn_pos
    intervalCenter := intCent
    radius := fun _ => r
    radius_pos := fun _ => hr_pos
    witnessCenter := wc
    witnessCenter_mem_nearCritical := fun i => (wcChoice i).property
    wit := fun i => w (wcChoice i)
    two_fold_spacing := ?_
    I_subset_neighborhood := ?_
    covers := ?_ }⟩
  · -- two_fold_spacing: integer-gap ≥ 2 among kept indices.
    intro i h
    have hei_lt1 : (e i).val < (e ⟨i.val + 1, by omega⟩).val :=
      e.strictMono (by show i.val < i.val + 1; omega)
    have hei_lt2 : (e ⟨i.val + 1, by omega⟩).val < (e ⟨i.val + 2, h⟩).val :=
      e.strictMono (by show i.val + 1 < i.val + 2; omega)
    have hei_gap : (e i).val + 2 ≤ (e ⟨i.val + 2, h⟩).val := by omega
    have hei_val_diff : (2 : ℝ) ≤ ((e ⟨i.val + 2, h⟩).val : ℝ) - (e i).val := by
      have : ((e ⟨i.val + 2, h⟩).val : ℝ) ≥ (e i).val + 2 := by exact_mod_cast hei_gap
      linarith
    show ((e i).val : ℝ) / M + r < ((e ⟨i.val + 2, h⟩).val : ℝ) / M - r
    have h_diff_norm : ((e ⟨i.val + 2, h⟩).val : ℝ) / M - (e i).val / M =
        (((e ⟨i.val + 2, h⟩).val : ℝ) - (e i).val) / M := by ring
    have h_ge : (2 : ℝ) / M ≤ ((e ⟨i.val + 2, h⟩).val : ℝ) / M - (e i).val / M := by
      rw [h_diff_norm]
      exact div_le_div_of_nonneg_right hei_val_diff hM_real_pos.le
    have h_2_gt_2r : (2 : ℝ) / M > 2 * r := by
      show (2 : ℝ) / M > 2 * (2 / (3 * M))
      have h_2r_eq : 2 * (2 / (3 * (M : ℝ))) = 4 / (3 * M) := by ring
      rw [h_2r_eq, gt_iff_lt, div_lt_div_iff₀ (by positivity) hM_real_pos]
      linarith
    linarith
  · -- I_subset_neighborhood: s within r of intCent i ⇒ s within r+lam/4 < lam of nearestNC,
    -- ⇒ s ∈ ball (nearestNC i).val lam ⊆ U (wcChoice i) = (wit i).neighborhood.
    intro i s hs
    apply wcChoice_prop i
    simp only [Metric.mem_ball]
    have h_s_icc : dist s (intCent i) < r := by
      show |s.val - (intCent i).val| < r
      rw [abs_sub_lt_iff]; refine ⟨?_, ?_⟩ <;> linarith [hs.1, hs.2]
    have : dist s (nearestNC i).val ≤
        dist s (intCent i) + dist (intCent i) (nearestNC i).val :=
      dist_triangle _ _ _
    have hnd : dist (intCent i) (nearestNC i).val < lam / 4 := nearestNC_dist i
    linarith
  · -- covers: rounding lands in kept indices; x within 1/(2M) < r of that c_k.
    intro x hx
    obtain ⟨k, hk⟩ := round_bound x
    have hk_mem : k ∈ kept := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨x, hx⟩, ?_⟩
      exact lt_of_le_of_lt hk h_half_lt_quarter
    -- k is in the range of e (orderEmbOfFin hits exactly kept as a set).
    have h_range : (Set.range e : Set _) = (kept : Set _) :=
      kept.range_orderEmbOfFin rfl
    have : k ∈ Set.range e := by rw [h_range]; exact_mod_cast hk_mem
    obtain ⟨i, hi⟩ := this
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    show x.val ∈ Set.Ioo ((intCent i).val - r) ((intCent i).val + r)
    have hintCent_val : (intCent i).val = (c k).val := by
      show (c (e i)).val = (c k).val
      rw [hi]
    rw [hintCent_val]
    -- hk : dist (c k) x ≤ 1/(2M) ≤ 1/(2M) < r. So dist < r.
    have h_half_lt_r : (1 : ℝ) / (2 * M) < r := by
      show (1 : ℝ) / (2 * M) < 2 / (3 * M)
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]
      linarith
    have h_dist : |((c k).val : ℝ) - x.val| < r := lt_of_le_of_lt hk h_half_lt_r
    rw [abs_sub_lt_iff] at h_dist
    exact ⟨by linarith [h_dist.2], by linarith [h_dist.1]⟩

end CombArg.OneDim
