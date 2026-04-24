/-
Copyright (c) 2026 Xinze Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xinze Li
-/
import CombLemma.Refinement.InitialCover

/-!
# Step 1 — Disjointness via chain spacing and parity rescue

Spacing condition (a) of an `InitialCover` iterates into a chain bound
on indices with gap `2 * (m + 1)`; the chain bound yields disjointness
of `ic.I i` and `ic.I j` at even gaps, and hence disjointness of their
closures. A parity argument then shows that for three sorted distinct
indices, some pair has even gap ≥ 2, which rules out any point lying
in all three closures — the ingredient that powers `terminal_twoFold`
(see `docs/design-notes.md §11`).

* `InitialCover.chain_spacing` — iterated spacing (a) at gap `2(m+1)`.
* `InitialCover.disjoint_of_even_gap` — open-interval disjointness.
* `InitialCover.closure_disjoint_of_even_gap` — closed-interval
  disjointness.
* `InitialCover.not_three_overlap` — parity rescue: no point
  lies in three `closure (ic.I _)` at distinct sorted indices.
-/

namespace CombLemma.Refinement

open CombLemma

namespace InitialCover

/-! ## Even-gap disjointness of `I_i`

The strongest disjointness statement provable from `InitialCover`'s
abstract fields is for pairs of indices whose gap is an **even** integer
≥ 2. A counter-example shows that for a gap that is odd and ≥ 3 with
non-monotone centers (permitted by the structure), `I_i ∩ I_j` can be
nonempty. Parity forces that for any three distinct indices `a < b < c`,
*some* pair in `{(a,b), (b,c), (a,c)}` has even gap ≥ 2, so even-gap
disjointness suffices to derive `twoFold` via
`not_three_overlap` (see `docs/design-notes.md §11`). -/

/-- **Chain spacing**: for `m ≥ 1` and indices `i, j : Fin ic.n` with
`j.val = i.val + 2 * m`, spacing (a) iterated `m` times gives
`(intervalCenter i).val + radius i < (intervalCenter j).val -
radius j`. Hence `Disjoint (ic.I i) (ic.I j)`. -/
lemma chain_spacing
    {X : Type*} [PseudoMetricSpace X] [PairableCover X]
    {f : unitInterval → ℝ} {m₀ : ℝ} {N : ℕ}
    (ic : InitialCover (X := X) f m₀ N) (i : Fin ic.n) :
    ∀ (m : ℕ) (j : Fin ic.n), j.val = i.val + 2 * (m + 1) →
      (ic.intervalCenter i).val + ic.radius i <
        (ic.intervalCenter j).val - ic.radius j := by
  intro m
  induction m with
  | zero =>
    intro j h_gap
    have h_bound : i.val + 2 < ic.n := by
      have : j.val < ic.n := j.isLt
      omega
    have h_fin_eq : j = (⟨i.val + 2, h_bound⟩ : Fin ic.n) := by
      apply Fin.ext
      simp [h_gap]
    rw [h_fin_eq]
    exact ic.two_fold_spacing i h_bound
  | succ k ih =>
    intro j h_gap
    have h_mid_bound : i.val + 2 * (k + 1) < ic.n := by
      have : j.val < ic.n := j.isLt
      omega
    let j_mid : Fin ic.n := ⟨i.val + 2 * (k + 1), h_mid_bound⟩
    have h_j_mid : j_mid.val = i.val + 2 * (k + 1) := rfl
    have h_ih := ih j_mid h_j_mid
    have h_plus_bound : j_mid.val + 2 < ic.n := by
      show i.val + 2 * (k + 1) + 2 < ic.n
      have : j.val < ic.n := j.isLt
      omega
    have h_spacing_mid := ic.two_fold_spacing j_mid h_plus_bound
    have hr_pos : 0 < ic.radius j_mid := ic.radius_pos j_mid
    have h_fin_eq : j = (⟨j_mid.val + 2, h_plus_bound⟩ : Fin ic.n) := by
      apply Fin.ext
      show j.val = j_mid.val + 2
      rw [h_j_mid, h_gap]
      ring
    rw [h_fin_eq]
    linarith [h_ih, h_spacing_mid, hr_pos]

/-- Even-gap disjointness: if `j.val - i.val = 2 * (m + 1)`, then
`ic.I i` and `ic.I j` are disjoint. -/
lemma disjoint_of_even_gap
    {X : Type*} [PseudoMetricSpace X] [PairableCover X]
    {f : unitInterval → ℝ} {m₀ : ℝ} {N : ℕ}
    (ic : InitialCover (X := X) f m₀ N) (i j : Fin ic.n)
    (m : ℕ) (h_gap : j.val = i.val + 2 * (m + 1)) :
    Disjoint (ic.I i) (ic.I j) := by
  have h_strict := ic.chain_spacing i m j h_gap
  rw [Set.disjoint_iff]
  intro t ht
  simp only [InitialCover.I, Set.mem_inter_iff, Set.mem_preimage,
    Set.mem_Ioo] at ht
  obtain ⟨⟨_, h1⟩, ⟨h2, _⟩⟩ := ht
  -- h1: t.val < (intervalCenter i).val + radius i
  -- h2: (intervalCenter j).val - radius j < t.val
  -- h_strict: (intervalCenter i).val + radius i < (intervalCenter j).val - radius j
  linarith

/-- Closed-interval version of `disjoint_of_even_gap`: even-gap
indices have disjoint `closure (ic.I _)`. The strict-`<` spacing from
`chain_spacing` gives disjoint *closed* intervals. -/
lemma closure_disjoint_of_even_gap
    {X : Type*} [PseudoMetricSpace X] [PairableCover X]
    {f : unitInterval → ℝ} {m₀ : ℝ} {N : ℕ}
    (ic : InitialCover (X := X) f m₀ N) (i j : Fin ic.n)
    (m : ℕ) (h_gap : j.val = i.val + 2 * (m + 1)) :
    Disjoint (closure (ic.I i)) (closure (ic.I j)) := by
  have h_strict := ic.chain_spacing i m j h_gap
  rw [Set.disjoint_iff]
  intro t ⟨ht_i, ht_j⟩
  -- closure(ic.I x) ⊆ preimage of Icc.
  have h_cl : ∀ x : Fin ic.n, closure (ic.I x) ⊆
      Subtype.val ⁻¹'
        Set.Icc ((ic.intervalCenter x).val - ic.radius x)
                ((ic.intervalCenter x).val + ic.radius x) := by
    intro x
    apply closure_minimal
    · intro s hs
      simp only [InitialCover.I, Set.mem_preimage, Set.mem_Ioo] at hs
      simp only [Set.mem_preimage, Set.mem_Icc]
      exact ⟨le_of_lt hs.1, le_of_lt hs.2⟩
    · exact isClosed_Icc.preimage continuous_subtype_val
  have hi_bound := h_cl i ht_i
  have hj_bound := h_cl j ht_j
  simp only [Set.mem_preimage, Set.mem_Icc] at hi_bound hj_bound
  linarith [hi_bound.2, hj_bound.1]

/-- **Parity rescue**: given three indices sorted by `.val`, some pair
has even gap ≥ 2, so the `ic.I`-closures at the three indices cannot
all contain a common point. Consumed by `terminal_twoFold`. -/
lemma not_three_overlap
    {X : Type*} [PseudoMetricSpace X] [PairableCover X]
    {f : unitInterval → ℝ} {m₀ : ℝ} {N : ℕ}
    (ic : InitialCover (X := X) f m₀ N)
    (a b c : Fin ic.n) (hab : a.val < b.val) (hbc : b.val < c.val)
    (t : unitInterval)
    (ha : t ∈ closure (ic.I a)) (hb : t ∈ closure (ic.I b))
    (hc : t ∈ closure (ic.I c)) :
    False := by
  by_cases h_ca_even : (c.val - a.val) % 2 = 0
  · -- c.val - a.val even ≥ 2 → (a, c) disjoint
    have h_gap_ge : 2 ≤ c.val - a.val := by omega
    refine (Set.disjoint_iff.mp
      (ic.closure_disjoint_of_even_gap a c ((c.val - a.val) / 2 - 1) ?_)) ⟨ha, hc⟩
    omega
  · have h_ca_ge_3 : 3 ≤ c.val - a.val := by omega
    by_cases h_ab_even : (b.val - a.val) % 2 = 0
    · -- (a, b) even ≥ 2
      have h_ab_ge : 2 ≤ b.val - a.val := by omega
      refine (Set.disjoint_iff.mp
        (ic.closure_disjoint_of_even_gap a b ((b.val - a.val) / 2 - 1) ?_)) ⟨ha, hb⟩
      omega
    · -- (b, c) even ≥ 2
      have h_bc_even : (c.val - b.val) % 2 = 0 := by omega
      have h_bc_ge : 2 ≤ c.val - b.val := by omega
      refine (Set.disjoint_iff.mp
        (ic.closure_disjoint_of_even_gap b c ((c.val - b.val) / 2 - 1) ?_)) ⟨hb, hc⟩
      omega

end InitialCover

end CombLemma.Refinement
