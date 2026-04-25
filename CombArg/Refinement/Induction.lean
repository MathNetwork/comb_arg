/-
Copyright (c) 2026 Xinze Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xinze Li
-/
import CombArg.Refinement.PartialRefinement

/-!
# Step 1 — Inductive step + termination

* `step_succ_at` — extend a `PartialRefinement ic (l+1)` to
  `PartialRefinement ic (l+2)` by appending a new piece labelled
  `i_star`. Two-case dispatch on the paper's predicate
  `ic.I i_star ⊆ pr.J prev ∪ ic.I (pr.σ prev)`. Returns an
  `ExtendResult` bundling the extended refinement together with
  the four downstream invariants
  (`J_castSucc` / `σ_castSucc` / `σ_last` / `covers_i_star`)
  the termination proof needs.
* `exists_terminal_refinement` — bounded iteration of
  `step_succ_at` from `step_zero`: at most `ic.n` extensions
  yield a terminal `PartialRefinement ic L` with `σ` injective
  and every `ic.I i ⊆ ⋃ pr.J k`.

The paper's smallest-index choice (`Finset.min'` over the
remaining indices) lives in `exists_terminal_refinement_aux`'s
control flow rather than inside `step_succ_at`: the termination
proof needs explicit access to the chosen index, so the index is
threaded through as a parameter.
-/

namespace CombArg.Refinement

open CombArg
open scoped Classical

variable {f : unitInterval → ℝ} {m₀ : ℝ} {N : ℕ}

/-! ## `ExtendResult`: bundled output of one inductive step

The output of `extend_refinement` (and hence of `step_succ_at`)
combines the extended `PartialRefinement` with four downstream
invariants. Bundling them as a structure rather than a 5-tuple
gives the termination proof named-field access in place of
`.property.2.2.1`-style projections. -/

/-- Bundled output of one inductive-step extension: the new
`PartialRefinement` together with the four invariants relating it
to the old one. -/
private structure ExtendResult
    {ic : InitialCover f m₀ N} {l : ℕ}
    (pr : PartialRefinement ic (l + 1))
    (i_star : Fin ic.n) where
  /-- The extended refinement, length `l + 2`. -/
  pr' : PartialRefinement ic (l + 2)
  /-- Old pieces survive at their `castSucc`-embedded indices. -/
  J_castSucc : ∀ k' : Fin (l + 1), pr'.J k'.castSucc = pr.J k'
  /-- Old labels survive at their `castSucc`-embedded indices. -/
  σ_castSucc : ∀ k' : Fin (l + 1), pr'.σ k'.castSucc = pr.σ k'
  /-- The new label at the last slot is `i_star`. -/
  σ_last : pr'.σ (Fin.last (l + 1)) = i_star
  /-- The piece at index `i_star` is now covered by the union. -/
  covers_i_star : ic.I i_star ⊆ ⋃ k : Fin (l + 2), pr'.J k

/-! ## `extend_refinement`: shared builder

Given a `Jnew` satisfying `Jnew ⊆ ic.I i_star` and
`ic.I i_star ⊆ Jnew ∪ ⋃ pr.J k'`, produce an `ExtendResult` with
`J_{l+1} := Jnew`, `σ_{l+1} := i_star`. The `J_subset` and
`processed_cover` invariants of the new `PartialRefinement` are
discharged uniformly from the two subset hypotheses. -/

/-- Common builder for the inductive step. -/
private noncomputable def extend_refinement
    {ic : InitialCover f m₀ N} {l : ℕ}
    (pr : PartialRefinement ic (l + 1))
    (i_star : Fin ic.n)
    (Jnew : Set unitInterval)
    (hJsub : Jnew ⊆ ic.I i_star)
    (hcover : ic.I i_star ⊆ Jnew ∪ ⋃ k' : Fin (l + 1), pr.J k') :
    ExtendResult pr i_star where
  pr' :=
    { J := Fin.lastCases Jnew pr.J
      σ := Fin.lastCases i_star pr.σ
      J_subset := by
        intro k
        induction k using Fin.lastCases with
        | last =>
          simp only [Fin.lastCases_last]
          exact hJsub
        | cast k' =>
          simp only [Fin.lastCases_castSucc]
          exact pr.J_subset k'
      processed_cover := by
        intro k t ht
        induction k using Fin.lastCases with
        | last =>
          simp only [Fin.lastCases_last] at ht
          rcases hcover ht with h_new | h_old
          · exact Set.mem_iUnion.mpr ⟨Fin.last (l + 1), by
              simp only [Fin.lastCases_last]; exact h_new⟩
          · obtain ⟨k'', hk''⟩ := Set.mem_iUnion.mp h_old
            exact Set.mem_iUnion.mpr ⟨k''.castSucc, by
              simp only [Fin.lastCases_castSucc]; exact hk''⟩
        | cast k' =>
          simp only [Fin.lastCases_castSucc] at ht
          obtain ⟨k'', hk''⟩ :=
            Set.mem_iUnion.mp (pr.processed_cover k' ht)
          exact Set.mem_iUnion.mpr ⟨k''.castSucc, by
            simp only [Fin.lastCases_castSucc]; exact hk''⟩ }
  J_castSucc := fun k' =>
    show Fin.lastCases Jnew pr.J k'.castSucc = pr.J k' from
      Fin.lastCases_castSucc k'
  σ_castSucc := fun k' =>
    show Fin.lastCases i_star pr.σ k'.castSucc = pr.σ k' from
      Fin.lastCases_castSucc k'
  σ_last :=
    show Fin.lastCases i_star pr.σ (Fin.last (l + 1)) = i_star from
      Fin.lastCases_last
  covers_i_star := by
    intro t ht
    rcases hcover ht with h_new | h_old
    · refine Set.mem_iUnion.mpr ⟨Fin.last (l + 1), ?_⟩
      show Fin.lastCases Jnew pr.J (Fin.last (l + 1)) t
      simp only [Fin.lastCases_last]; exact h_new
    · obtain ⟨k'', hk''⟩ := Set.mem_iUnion.mp h_old
      refine Set.mem_iUnion.mpr ⟨k''.castSucc, ?_⟩
      show Fin.lastCases Jnew pr.J k''.castSucc t
      simp only [Fin.lastCases_castSucc]; exact hk''

/-! ## `step_succ_at`: paper-faithful two-case dispatch

DLT §3.2 Step 1's induction at parameter `i_star`. Case-split on
the paper's predicate `ic.I i_star ⊆ pr.J prev ∪ ic.I (pr.σ prev)`:

* **Case 1** (predicate holds): `Jnew := ic.I i_star`.
  `J_subset` is `subset_refl`; `hcover` is `Or.inl`.
* **Case 2** (predicate fails): `Jnew := ic.I i_star \ ic.I (pr.σ prev)`.
  `J_subset` via `Set.diff_subset`; `hcover` uses
  `pr.processed_cover prev` to handle the part of `ic.I i_star`
  that lies inside `ic.I (pr.σ prev)`. -/

/-- Inductive step at an explicit index. -/
noncomputable def step_succ_at
    {ic : InitialCover f m₀ N} {l : ℕ}
    (pr : PartialRefinement ic (l + 1))
    (i_star : Fin ic.n) :
    ExtendResult pr i_star := by
  let prev : Fin (l + 1) := Fin.last l
  by_cases hcase1 : ic.I i_star ⊆ pr.J prev ∪ ic.I (pr.σ prev)
  · -- Case 1: Jnew := ic.I i_star.
    exact extend_refinement pr i_star (ic.I i_star) (subset_refl _)
      (fun _ ht => Or.inl ht)
  · -- Case 2: Jnew := ic.I i_star \ ic.I (pr.σ prev).
    refine extend_refinement pr i_star (ic.I i_star \ ic.I (pr.σ prev))
      Set.diff_subset ?_
    intro t ht
    by_cases h_in_prev : t ∈ ic.I (pr.σ prev)
    · exact Or.inr (pr.processed_cover prev h_in_prev)
    · exact Or.inl ⟨ht, h_in_prev⟩

/-! ## Termination iteration -/

/-- **Termination core** — bounded iteration of `step_succ_at`.
Given a `PartialRefinement` of length `l + 1` with injective `σ`
and a budget `k` that bounds the remaining (uncovered) index
count, produce a terminal refinement. Proof by induction on `k`. -/
private lemma exists_terminal_refinement_aux
    {ic : InitialCover f m₀ N} :
    ∀ (k l : ℕ) (pr : PartialRefinement ic (l + 1)),
      Function.Injective pr.σ →
      (Finset.univ.filter
        (fun i : Fin ic.n => ¬ (ic.I i ⊆ ⋃ k' : Fin (l + 1), pr.J k'))).card ≤ k →
      ∃ L : ℕ, ∃ pr' : PartialRefinement ic L,
        Function.Injective pr'.σ ∧
        ∀ i : Fin ic.n, ic.I i ⊆ ⋃ j : Fin L, pr'.J j := by
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
      let result := step_succ_at pr i_star
      let pr' : PartialRefinement ic (l + 2) := result.pr'
      -- i_star ≠ pr.σ k' for all k': from h_uncov + processed_cover.
      have h_i_star_fresh : ∀ k' : Fin (l + 1), pr.σ k' ≠ i_star := by
        intro k' h_eq
        apply h_uncov
        rw [← h_eq]
        exact pr.processed_cover k'
      -- σ' injective via Fin.lastCases case analysis.
      have hσ' : Function.Injective pr'.σ := by
        intro a b hab
        induction a using Fin.lastCases with
        | last =>
          induction b using Fin.lastCases with
          | last => rfl
          | cast b' =>
            rw [result.σ_last, result.σ_castSucc] at hab
            exact (h_i_star_fresh b' hab.symm).elim
        | cast a' =>
          induction b using Fin.lastCases with
          | last =>
            rw [result.σ_last, result.σ_castSucc] at hab
            exact (h_i_star_fresh a' hab).elim
          | cast b' =>
            rw [result.σ_castSucc, result.σ_castSucc] at hab
            have := hσ hab
            rw [this]
      -- Show new remaining.card ≤ n.
      set old_rem : Finset (Fin ic.n) := Finset.univ.filter
        (fun i : Fin ic.n => ¬ (ic.I i ⊆ ⋃ k' : Fin (l + 1), pr.J k'))
      set new_rem : Finset (Fin ic.n) := Finset.univ.filter
        (fun i : Fin ic.n => ¬ (ic.I i ⊆ ⋃ k' : Fin (l + 2), pr'.J k'))
      have h_i_star_old : i_star ∈ old_rem :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, h_uncov⟩
      have h_i_star_new : i_star ∉ new_rem := by
        intro hi
        have h_not_cov : ¬ (ic.I i_star ⊆ ⋃ k' : Fin (l + 2), pr'.J k') :=
          (Finset.mem_filter.mp hi).2
        exact h_not_cov result.covers_i_star
      have h_sub : new_rem ⊆ old_rem := by
        intro i hi
        have h_not_new : ¬ (ic.I i ⊆ ⋃ k' : Fin (l + 2), pr'.J k') :=
          (Finset.mem_filter.mp hi).2
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        intro h_old
        apply h_not_new
        intro t ht
        obtain ⟨k', hk'⟩ := Set.mem_iUnion.mp (h_old ht)
        refine Set.mem_iUnion.mpr ⟨k'.castSucc, ?_⟩
        rw [result.J_castSucc]
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

/-- Iterating `step_succ_at` from `step_zero` eventually yields a
`PartialRefinement` whose pieces cover every `ic.I i` AND whose
`σ` is injective. Proof by strong induction on `remaining.card`,
delegated to `exists_terminal_refinement_aux`. -/
lemma exists_terminal_refinement
    (ic : InitialCover f m₀ N) :
    ∃ L : ℕ, ∃ pr : PartialRefinement ic L,
      Function.Injective pr.σ ∧
      ∀ i : Fin ic.n, ic.I i ⊆ ⋃ k : Fin L, pr.J k := by
  refine exists_terminal_refinement_aux ic.n 0 (step_zero ic) ?_ ?_
  · -- step_zero has σ = constant on Fin 1 — trivially injective.
    intro a b _
    apply Fin.ext
    have ha : a.val < 1 := a.isLt
    have hb : b.val < 1 := b.isLt
    omega
  · -- remaining.card ≤ |Fin ic.n| = ic.n.
    have h1 : (Finset.univ.filter
          (fun i : Fin ic.n =>
            ¬ (ic.I i ⊆ ⋃ k' : Fin 1, (step_zero ic).J k'))).card
        ≤ (Finset.univ : Finset (Fin ic.n)).card :=
      Finset.card_filter_le _ _
    rw [Finset.card_univ, Fintype.card_fin] at h1
    exact h1

end CombArg.Refinement
