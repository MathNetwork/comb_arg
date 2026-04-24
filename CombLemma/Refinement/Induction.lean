/-
Copyright (c) 2026 Xinze Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xinze Li
-/
import CombLemma.Refinement.PartialRefinement
import Mathlib.Data.Finset.Max

/-!
# Step 1 — Inductive step + termination

* `step_succ` — paper-faithful smallest-index version of the inductive
  step. Selects `i_star` via `Finset.min'` internally and dispatches on
  the paper's case predicate.
* `step_succ_at` — explicit-`i_star` version returning a `Subtype` that
  bundles the "`i_star` gets covered" property. Used by the termination
  proof which needs external access to the chosen index.
* `exists_terminal_refinement` — bounded iteration on `remaining.card`:
  starting from `step_zero`, iterating `step_succ_at` at most `ic.n`
  times yields a terminal `PartialRefinement ic L` with `σ` injective
  and every `ic.I i ⊆ ⋃ pr.J k`.
-/

namespace CombLemma.Refinement

open CombLemma
open scoped Classical

/-! ## Inductive step `step_succ` -/

/-- **Inductive step**: extend a `PartialRefinement ic (l+1)` to
`PartialRefinement ic (l+2)` by DLT Step 1's smallest-index
selection + two-case dispatch.

Takes `pr : PartialRefinement ic (l+1)` (so `prev := Fin.last l`
is always defined) and a proof that some `i_star ∈ Fin ic.n` has
`ic.I i_star ⊄ ⋃ pr.J k` (otherwise we'd terminate).

Selects `i_star := min` over the remaining indices via `Finset.min'`.
Case split on paper's predicate
`ic.I i_star ⊆ pr.J prev ∪ ic.I (pr.σ prev)`:

* **Case 1** (predicate holds): `J (l+1) := ic.I i_star`,
  `σ (l+1) := i_star`. Both invariants discharge directly.
* **Case 2** (predicate fails): `J (l+1) := ic.I i_star \
  ic.I (pr.σ prev)`, `σ (l+1) := i_star`. `J_subset` via
  `Set.diff_subset`; `processed_cover` for the new piece uses the
  decomposition
  `ic.I i_star = (ic.I i_star ∩ ic.I (σ prev)) ∪ (ic.I i_star \ ic.I (σ prev))`
  with the first part handled by `pr.processed_cover prev`. -/
noncomputable def step_succ
    {X : Type*} [PseudoMetricSpace X] [PairableCover X]
    {f : unitInterval → ℝ} {m₀ : ℝ} {N : ℕ}
    {ic : InitialCover (X := X) f m₀ N} {l : ℕ}
    (pr : PartialRefinement ic (l + 1))
    (h_remaining : ∃ i : Fin ic.n,
        ¬ (ic.I i ⊆ ⋃ k : Fin (l + 1), pr.J k)) :
    PartialRefinement ic (l + 2) := by
  -- Previous piece index.
  let prev : Fin (l + 1) := Fin.last l
  -- Filter-find the smallest uncovered index.
  let remaining : Finset (Fin ic.n) :=
    Finset.univ.filter
      (fun i => ¬ (ic.I i ⊆ ⋃ k : Fin (l + 1), pr.J k))
  have h_ne : remaining.Nonempty := by
    obtain ⟨i, hi⟩ := h_remaining
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  let i_star : Fin ic.n := remaining.min' h_ne
  have h_i_star_mem : i_star ∈ remaining := remaining.min'_mem h_ne
  -- Case split on the paper's predicate.
  by_cases hcase1 : ic.I i_star ⊆ pr.J prev ∪ ic.I (pr.σ prev)
  · -- Case 1: J_{l+1} := ic.I i_star; σ_{l+1} := i_star.
    refine {
      J := Fin.lastCases (ic.I i_star) pr.J
      σ := Fin.lastCases i_star pr.σ
      J_subset := ?_
      processed_cover := ?_ }
    · -- J_subset
      intro k
      induction k using Fin.lastCases with
      | last =>
        simp only [Fin.lastCases_last]
        exact subset_refl _
      | cast k' =>
        simp only [Fin.lastCases_castSucc]
        exact pr.J_subset k'
    · -- processed_cover
      intro k t ht
      induction k using Fin.lastCases with
      | last =>
        -- σ(last) = i_star; ic.I i_star ⊆ ⋃ new J (the last slot is ic.I i_star).
        simp only [Fin.lastCases_last] at ht
        refine Set.mem_iUnion.mpr ⟨Fin.last (l + 1), ?_⟩
        simp only [Fin.lastCases_last]
        exact ht
      | cast k' =>
        simp only [Fin.lastCases_castSucc] at ht
        have h_old := pr.processed_cover k' ht
        obtain ⟨k'', hk''⟩ := Set.mem_iUnion.mp h_old
        refine Set.mem_iUnion.mpr ⟨k''.castSucc, ?_⟩
        simp only [Fin.lastCases_castSucc]
        exact hk''
  · -- Case 2: J_{l+1} := ic.I i_star \ ic.I (pr.σ prev); σ_{l+1} := i_star.
    refine {
      J := Fin.lastCases (ic.I i_star \ ic.I (pr.σ prev)) pr.J
      σ := Fin.lastCases i_star pr.σ
      J_subset := ?_
      processed_cover := ?_ }
    · -- J_subset
      intro k
      induction k using Fin.lastCases with
      | last =>
        simp only [Fin.lastCases_last]
        exact Set.diff_subset
      | cast k' =>
        simp only [Fin.lastCases_castSucc]
        exact pr.J_subset k'
    · -- processed_cover
      intro k t ht
      induction k using Fin.lastCases with
      | last =>
        -- σ(last) = i_star.
        -- Goal: t ∈ ⋃ new J.
        -- Decompose by `t ∈ ic.I (pr.σ prev)` or not.
        simp only [Fin.lastCases_last] at ht
        by_cases h_in_prev : t ∈ ic.I (pr.σ prev)
        · -- Use pr.processed_cover prev.
          have h_old := pr.processed_cover prev h_in_prev
          obtain ⟨k'', hk''⟩ := Set.mem_iUnion.mp h_old
          refine Set.mem_iUnion.mpr ⟨k''.castSucc, ?_⟩
          simp only [Fin.lastCases_castSucc]
          exact hk''
        · -- t ∈ ic.I i_star \ ic.I (pr.σ prev) = new J (Fin.last).
          refine Set.mem_iUnion.mpr ⟨Fin.last (l + 1), ?_⟩
          simp only [Fin.lastCases_last]
          exact ⟨ht, h_in_prev⟩
      | cast k' =>
        simp only [Fin.lastCases_castSucc] at ht
        have h_old := pr.processed_cover k' ht
        obtain ⟨k'', hk''⟩ := Set.mem_iUnion.mp h_old
        refine Set.mem_iUnion.mpr ⟨k''.castSucc, ?_⟩
        simp only [Fin.lastCases_castSucc]
        exact hk''

/-! ## Termination iteration via bounded `Nat.rec`

`step_succ` picks `i_star` via `Finset.min'` internally. For the
termination proof we need external access to the chosen index, so
`step_succ_at` is parameterized by `i_star` explicitly. The body is a
**term-mode** structure literal with
`σ := Fin.lastCases i_star pr.σ` uniformly in both cases (the only
difference between cases is the `J` field), which makes
`step_succ_at_sigma_last` reduce by `Fin.lastCases_last`. -/

/-- Inductive step parameterized by an explicit uncovered index,
bundled with the "`i_star` gets covered" property. Returning a
`Subtype` (result + property) avoids post-hoc unfolding of the
tactic-mode `by_cases` dispatch. -/
noncomputable def step_succ_at
    {X : Type*} [PseudoMetricSpace X] [PairableCover X]
    {f : unitInterval → ℝ} {m₀ : ℝ} {N : ℕ}
    {ic : InitialCover (X := X) f m₀ N} {l : ℕ}
    (pr : PartialRefinement ic (l + 1))
    (i_star : Fin ic.n)
    (_h_uncov : ¬ (ic.I i_star ⊆ ⋃ k : Fin (l + 1), pr.J k)) :
    { pr' : PartialRefinement ic (l + 2) //
      (∀ k' : Fin (l + 1), pr'.J k'.castSucc = pr.J k') ∧
      (∀ k' : Fin (l + 1), pr'.σ k'.castSucc = pr.σ k') ∧
      pr'.σ (Fin.last (l + 1)) = i_star ∧
      ic.I i_star ⊆ ⋃ k : Fin (l + 2), pr'.J k } := by
  let prev : Fin (l + 1) := Fin.last l
  by_cases hcase1 : ic.I i_star ⊆ pr.J prev ∪ ic.I (pr.σ prev)
  · -- Case 1: J_{l+1} := ic.I i_star.
    refine ⟨{
      J := Fin.lastCases (ic.I i_star) pr.J
      σ := Fin.lastCases i_star pr.σ
      J_subset := ?_
      processed_cover := ?_ }, ?_, ?_, ?_, ?_⟩
    · intro k
      induction k using Fin.lastCases with
      | last => simp only [Fin.lastCases_last]; exact subset_refl _
      | cast k' => simp only [Fin.lastCases_castSucc]; exact pr.J_subset k'
    · intro k t ht
      induction k using Fin.lastCases with
      | last =>
        simp only [Fin.lastCases_last] at ht
        refine Set.mem_iUnion.mpr ⟨Fin.last (l + 1), ?_⟩
        simp only [Fin.lastCases_last]; exact ht
      | cast k' =>
        simp only [Fin.lastCases_castSucc] at ht
        have h_old := pr.processed_cover k' ht
        obtain ⟨k'', hk''⟩ := Set.mem_iUnion.mp h_old
        refine Set.mem_iUnion.mpr ⟨k''.castSucc, ?_⟩
        simp only [Fin.lastCases_castSucc]; exact hk''
    · intro k'
      show Fin.lastCases _ pr.J k'.castSucc = pr.J k'
      exact Fin.lastCases_castSucc k'
    · intro k'
      show Fin.lastCases _ pr.σ k'.castSucc = pr.σ k'
      exact Fin.lastCases_castSucc k'
    · show Fin.lastCases i_star pr.σ (Fin.last (l + 1)) = i_star
      simp only [Fin.lastCases_last]
    · -- covered: ic.I i_star = J (Fin.last), so directly in the union.
      intro t ht
      refine Set.mem_iUnion.mpr ⟨Fin.last (l + 1), ?_⟩
      simp only [Fin.lastCases_last]; exact ht
  · -- Case 2: J_{l+1} := ic.I i_star \ ic.I (pr.σ prev).
    refine ⟨{
      J := Fin.lastCases (ic.I i_star \ ic.I (pr.σ prev)) pr.J
      σ := Fin.lastCases i_star pr.σ
      J_subset := ?_
      processed_cover := ?_ }, ?_, ?_, ?_, ?_⟩
    · intro k
      induction k using Fin.lastCases with
      | last => simp only [Fin.lastCases_last]; exact Set.diff_subset
      | cast k' => simp only [Fin.lastCases_castSucc]; exact pr.J_subset k'
    · intro k t ht
      induction k using Fin.lastCases with
      | last =>
        simp only [Fin.lastCases_last] at ht
        by_cases h_in_prev : t ∈ ic.I (pr.σ prev)
        · have h_old := pr.processed_cover prev h_in_prev
          obtain ⟨k'', hk''⟩ := Set.mem_iUnion.mp h_old
          refine Set.mem_iUnion.mpr ⟨k''.castSucc, ?_⟩
          simp only [Fin.lastCases_castSucc]; exact hk''
        · refine Set.mem_iUnion.mpr ⟨Fin.last (l + 1), ?_⟩
          simp only [Fin.lastCases_last]; exact ⟨ht, h_in_prev⟩
      | cast k' =>
        simp only [Fin.lastCases_castSucc] at ht
        have h_old := pr.processed_cover k' ht
        obtain ⟨k'', hk''⟩ := Set.mem_iUnion.mp h_old
        refine Set.mem_iUnion.mpr ⟨k''.castSucc, ?_⟩
        simp only [Fin.lastCases_castSucc]; exact hk''
    · intro k'
      show Fin.lastCases _ pr.J k'.castSucc = pr.J k'
      exact Fin.lastCases_castSucc k'
    · intro k'
      show Fin.lastCases _ pr.σ k'.castSucc = pr.σ k'
      exact Fin.lastCases_castSucc k'
    · show Fin.lastCases i_star pr.σ (Fin.last (l + 1)) = i_star
      simp only [Fin.lastCases_last]
    · -- covered: decompose t ∈ ic.I i_star by whether t ∈ ic.I (pr.σ prev).
      intro t ht
      by_cases h_in_prev : t ∈ ic.I (pr.σ prev)
      · have h_old := pr.processed_cover prev h_in_prev
        obtain ⟨k'', hk''⟩ := Set.mem_iUnion.mp h_old
        refine Set.mem_iUnion.mpr ⟨k''.castSucc, ?_⟩
        simp only [Fin.lastCases_castSucc]; exact hk''
      · refine Set.mem_iUnion.mpr ⟨Fin.last (l + 1), ?_⟩
        simp only [Fin.lastCases_last]; exact ⟨ht, h_in_prev⟩

/-- Iterating `step_succ_at` from `step_zero` eventually yields a
`PartialRefinement` whose pieces cover every `ic.I i` AND whose
`σ` is injective. Proof by strong induction on `remaining.card`. -/
lemma exists_terminal_refinement
    {X : Type*} [PseudoMetricSpace X] [PairableCover X]
    {f : unitInterval → ℝ} {m₀ : ℝ} {N : ℕ}
    (ic : InitialCover (X := X) f m₀ N) :
    ∃ L : ℕ, ∃ pr : PartialRefinement ic L,
      Function.Injective pr.σ ∧
      ∀ i : Fin ic.n, ic.I i ⊆ ⋃ k : Fin L, pr.J k := by
  suffices aux : ∀ (k l : ℕ) (pr : PartialRefinement ic (l + 1))
      (_hσ : Function.Injective pr.σ),
      (Finset.univ.filter
        (fun i : Fin ic.n => ¬ (ic.I i ⊆ ⋃ k' : Fin (l + 1), pr.J k'))).card ≤ k →
      ∃ L : ℕ, ∃ pr' : PartialRefinement ic L,
        Function.Injective pr'.σ ∧
        ∀ i : Fin ic.n, ic.I i ⊆ ⋃ j : Fin L, pr'.J j by
    refine aux ic.n 0 (step_zero ic) ?_ ?_
    · -- step_zero has σ = constant on Fin 1 — trivially injective.
      intro a b _
      apply Fin.ext
      have ha : a.val < 1 := a.isLt
      have hb : b.val < 1 := b.isLt
      omega
    · have h1 : (Finset.univ.filter
            (fun i : Fin ic.n =>
              ¬ (ic.I i ⊆ ⋃ k' : Fin 1, (step_zero ic).J k'))).card
          ≤ (Finset.univ : Finset (Fin ic.n)).card :=
        Finset.card_filter_le _ _
      rw [Finset.card_univ, Fintype.card_fin] at h1
      exact h1
  intro k
  induction k with
  | zero =>
    intro l pr hσ h_card
    refine ⟨l + 1, pr, hσ, ?_⟩
    intro i
    by_contra h_not
    have h_empty : (Finset.univ.filter
        (fun i' : Fin ic.n => ¬ (ic.I i' ⊆ ⋃ k' : Fin (l + 1), pr.J k'))) = ∅ :=
      Finset.card_eq_zero.mp (Nat.le_zero.mp h_card)
    have h_in : i ∈ Finset.univ.filter
        (fun i' : Fin ic.n => ¬ (ic.I i' ⊆ ⋃ k' : Fin (l + 1), pr.J k')) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, h_not⟩
    simp [h_empty] at h_in
  | succ n ih =>
    intro l pr hσ h_card
    by_cases h_rem : ∃ i : Fin ic.n,
        ¬ (ic.I i ⊆ ⋃ k' : Fin (l + 1), pr.J k')
    · let i_star := h_rem.choose
      have h_uncov : ¬ (ic.I i_star ⊆ ⋃ k' : Fin (l + 1), pr.J k') :=
        h_rem.choose_spec
      let result := step_succ_at pr i_star h_uncov
      let pr' : PartialRefinement ic (l + 2) := result.val
      have h_J_castSucc : ∀ k' : Fin (l + 1), pr'.J k'.castSucc = pr.J k' :=
        result.property.1
      have h_σ_castSucc : ∀ k' : Fin (l + 1), pr'.σ k'.castSucc = pr.σ k' :=
        result.property.2.1
      have h_σ_last : pr'.σ (Fin.last (l + 1)) = i_star :=
        result.property.2.2.1
      have h_i_covered : ic.I i_star ⊆ ⋃ k : Fin (l + 2), pr'.J k :=
        result.property.2.2.2
      -- i_star ≠ pr.σ k' for all k': from h_uncov + J_subset + processed_cover.
      have h_i_star_fresh : ∀ k' : Fin (l + 1), pr.σ k' ≠ i_star := by
        intro k' h_eq
        apply h_uncov
        rw [← h_eq]
        exact pr.processed_cover k'
      -- σ' injective: via Fin.lastCases case analysis.
      have hσ' : Function.Injective pr'.σ := by
        intro a b hab
        induction a using Fin.lastCases with
        | last =>
          induction b using Fin.lastCases with
          | last => rfl
          | cast b' =>
            rw [h_σ_last, h_σ_castSucc] at hab
            exact (h_i_star_fresh b' hab.symm).elim
        | cast a' =>
          induction b using Fin.lastCases with
          | last =>
            rw [h_σ_last, h_σ_castSucc] at hab
            exact (h_i_star_fresh a' hab).elim
          | cast b' =>
            rw [h_σ_castSucc, h_σ_castSucc] at hab
            have := hσ hab
            rw [this]
      -- Show new remaining.card ≤ n.
      set old_rem : Finset (Fin ic.n) := Finset.univ.filter
        (fun i : Fin ic.n => ¬ (ic.I i ⊆ ⋃ k' : Fin (l + 1), pr.J k')) with hor
      set new_rem : Finset (Fin ic.n) := Finset.univ.filter
        (fun i : Fin ic.n => ¬ (ic.I i ⊆ ⋃ k' : Fin (l + 2), pr'.J k')) with hnr
      have h_i_star_old : i_star ∈ old_rem :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, h_uncov⟩
      have h_i_star_new : i_star ∉ new_rem := by
        intro hi
        have h_not_cov : ¬ (ic.I i_star ⊆ ⋃ k' : Fin (l + 2), pr'.J k') :=
          (Finset.mem_filter.mp hi).2
        exact h_not_cov h_i_covered
      have h_sub : new_rem ⊆ old_rem := by
        intro i hi
        have h_not_new : ¬ (ic.I i ⊆ ⋃ k' : Fin (l + 2), pr'.J k') :=
          (Finset.mem_filter.mp hi).2
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        intro h_old
        apply h_not_new
        intro t ht
        have h_t_in_old := h_old ht
        obtain ⟨k', hk'⟩ := Set.mem_iUnion.mp h_t_in_old
        refine Set.mem_iUnion.mpr ⟨k'.castSucc, ?_⟩
        rw [h_J_castSucc]
        exact hk'
      have h_new_sub_erase : new_rem ⊆ old_rem.erase i_star := fun i hi =>
        Finset.mem_erase.mpr
          ⟨fun h_eq => h_i_star_new (h_eq ▸ hi), h_sub hi⟩
      have h_decrease : new_rem.card ≤ n := by
        calc new_rem.card
            ≤ (old_rem.erase i_star).card := Finset.card_le_card h_new_sub_erase
          _ = old_rem.card - 1 := Finset.card_erase_of_mem h_i_star_old
          _ ≤ (n + 1) - 1 := by omega
          _ = n := rfl
      exact ih (l + 1) pr' hσ' h_decrease
    · refine ⟨l + 1, pr, hσ, ?_⟩
      intro i
      by_contra h_not
      exact h_rem ⟨i, h_not⟩

end CombLemma.Refinement
