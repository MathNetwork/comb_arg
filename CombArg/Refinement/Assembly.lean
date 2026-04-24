/-
Copyright (c) 2026 Xinze Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xinze Li
-/
import CombArg.Core
import CombArg.Refinement.CoverConstruction
import CombArg.Refinement.Disjointness
import CombArg.Refinement.Induction
import CombArg.Util

/-!
# Combinatorial main theorem: Assembly into `FiniteCoverWithWitnesses`

This file packages the 1D cover-construction infrastructure into
the library's combinatorial main theorem `exists_refinement`: from
the witness hypothesis on `unitInterval` it constructs a
`FiniteCoverWithWitnesses unitInterval f m₀ (1/N) (1/(4N))`. The
scalar sup-reduction bookkeeping (downstream corollary
`CombArg.exists_sup_reduction_of_cover` and its one-parameter
specialization `CombArg.exists_sup_reduction`) is arithmetic over
the output structure.

* `terminal_twoFold` — if `σ` is injective then at most two pieces of
  a terminal `PartialRefinement` have `t` in their closure. Uses the
  parity-rescue argument `InitialCover.not_three_overlap`
  combined with `σ`-injectivity and the `J_subset` invariant.
* `saving_bound_closure` — the `LocalWitness` saving bound on the
  open neighborhood extends to the closure, via continuity of
  `replacementEnergy` and a sequence-limit argument.
* `exists_refinement` — **combinatorial main theorem**. From the
  witness hypothesis, assembles a `FiniteCoverWithWitnesses` by
  taking `piece k := closure (pr.J k)` and `saving k := 1/(4N)`
  uniform; `twoFold` via `terminal_twoFold`, `saving_bound` via
  `saving_bound_closure`.
-/

namespace CombArg.Refinement

open CombArg
open scoped Classical

variable {X : Type*} [PseudoMetricSpace X] [PairableCover X]
    {f : unitInterval → ℝ} {m₀ : ℝ} {N : ℕ}

/-! ## TwoFold derivation and saving_bound closure extension -/

/-- **TwoFold for terminal refinement**: if `σ` is injective then
every point lies in `closure (pr.J k)` for at most two indices `k`. -/
lemma terminal_twoFold
    {ic : InitialCover (X := X) f m₀ N} {L : ℕ}
    (pr : PartialRefinement ic L)
    (hσ : Function.Injective pr.σ)
    (t : unitInterval) :
    (Finset.univ.filter
      (fun k : Fin L => t ∈ closure (pr.J k))).card ≤ 2 := by
  by_contra h_not
  have h_gt : 2 < (Finset.univ.filter
      (fun k : Fin L => t ∈ closure (pr.J k))).card := by omega
  obtain ⟨k1, k2, k3, hk1, hk2, hk3, hk12, hk13, hk23⟩ :=
    Finset.two_lt_card_iff.mp h_gt
  have h1 : t ∈ closure (pr.J k1) := (Finset.mem_filter.mp hk1).2
  have h2 : t ∈ closure (pr.J k2) := (Finset.mem_filter.mp hk2).2
  have h3 : t ∈ closure (pr.J k3) := (Finset.mem_filter.mp hk3).2
  have h_clos_sub : ∀ k : Fin L,
      closure (pr.J k) ⊆ closure (ic.toSkippedSpacedIntervals.I (pr.σ k)) :=
    fun k => by
      simp only [ic.toSkippedSpacedIntervals_I]
      exact closure_mono (pr.J_subset k)
  have hd12v : (pr.σ k1).val ≠ (pr.σ k2).val :=
    fun h => hk12 (hσ (Fin.ext h))
  have hd13v : (pr.σ k1).val ≠ (pr.σ k3).val :=
    fun h => hk13 (hσ (Fin.ext h))
  have hd23v : (pr.σ k2).val ≠ (pr.σ k3).val :=
    fun h => hk23 (hσ (Fin.ext h))
  exact ic.toSkippedSpacedIntervals.not_three_overlap_any_order
    (pr.σ k1) (pr.σ k2) (pr.σ k3) hd12v hd13v hd23v t
    (h_clos_sub k1 h1) (h_clos_sub k2 h2) (h_clos_sub k3 h3)

/-- **Saving-bound extends to closure via continuity**. For `t` in
`closure (pr.J k)`, the inequality `f t − replacementEnergy t ≥
1/(4N)` holds, lifted from the open neighborhood where the
`LocalWitness.saving_bound` is known, through
`LocalWitness.replacementEnergy_continuous` + continuity of `f`. -/
lemma saving_bound_closure
    (hf : Continuous f)
    {ic : InitialCover (X := X) f m₀ N} {L : ℕ}
    (pr : PartialRefinement ic L) (k : Fin L)
    (t : unitInterval) (ht : t ∈ closure (pr.J k)) :
    f t - (ic.wit (pr.σ k)).replacementEnergy t ≥ 1 / (4 * (N : ℝ)) := by
  -- On `pr.J k ⊆ (ic.wit (pr.σ k)).neighborhood` the witness gives
  -- `(f − E) ≥ 1/(4N)`; this closed-half-line condition extends to
  -- `closure (pr.J k)` by continuity of `f − E`.
  refine ge_of_closure_of_ge
    (hf.sub (ic.wit (pr.σ k)).replacementEnergy_continuous)
    (fun s hs => (ic.wit (pr.σ k)).saving_bound s
      (ic.I_subset_neighborhood (pr.σ k) (pr.J_subset k hs))) ht

/-! ## Terminal target: `exists_refinement`

Specialized to `K = unitInterval` per `docs/design-notes.md §4`. The
abstract-`K` generalization is left to future work. -/

/-- **Combinatorial main theorem** (combinatorial core of
Almgren--Pitts for a 1D sweepout).

Given continuous `f : unitInterval → ℝ`, the hypothesis
`m₀ = sSup (range f)`, `N > 0`, and local witnesses at every
`1/N`-near-critical parameter, produces a
`FiniteCoverWithWitnesses unitInterval f m₀ (1/N) (1/(4N))`: a
finite family of closed pieces of `unitInterval` carrying
per-piece replacement energies `E_l` and uniform savings
`s_l = 1/(4N)`, satisfying
(I) `f − E_l ≥ s_l` on each piece;
(II) every `t` lies in at most two pieces (two-fold overlap);
(III) `{t : f t ≥ m₀ − 1/N} ⊆ ⋃ pieces`.

The existence of a scalar sup-reducing competitor `f'` follows
as a three-line bookkeeping corollary
(`CombArg.exists_sup_reduction_of_cover`,
`CombArg.exists_sup_reduction`); the non-trivial content is the
construction packaged here.

Chains the preceding infrastructure:

1. `exists_initialCover` → `InitialCover` with DLT spacing (a)+(b).
2. `exists_terminal_refinement` → terminal `PartialRefinement ic L`
   with `σ` injective and `∀ i, ic.I i ⊆ ⋃ pr.J k`.
3. Assemble `FiniteCoverWithWitnesses` with
   `piece k := closure (pr.J k)` and `saving k := 1/(4N)` uniform;
   `twoFold` via `terminal_twoFold`; `saving_bound` via
   `saving_bound_closure`. -/
lemma exists_refinement
    (hf : Continuous f)
    (hm : m₀ = sSup (Set.range f))
    (hN : 0 < N)
    (witness : ∀ t : unitInterval, f t ≥ m₀ - 1 / (N : ℝ) →
                 Nonempty (LocalWitness unitInterval X f t (1 / (4 * (N : ℝ))))) :
    Nonempty (FiniteCoverWithWitnesses unitInterval f m₀
              (1 / (N : ℝ)) (1 / (4 * (N : ℝ)))) := by
  -- Step 1: initial cover.
  obtain ⟨ic⟩ := exists_initialCover hf hm hN witness
  -- Step 2: iterate to terminal state.
  obtain ⟨L, pr, hσ_inj, h_terminal⟩ := exists_terminal_refinement ic
  -- Step 3: L ≥ 1 (else ic.I ⟨0, ic.n_pos⟩ ⊆ ∅, contradicting nonemptiness).
  have hL_pos : 0 < L := by
    by_contra h_not
    have hL_zero : L = 0 := by omega
    subst hL_zero
    have h_union_empty : (⋃ k : Fin 0, pr.J k) = (∅ : Set unitInterval) :=
      Set.iUnion_of_empty _
    have h_I_empty : ic.I ⟨0, ic.n_pos⟩ ⊆ ∅ := by
      rw [← h_union_empty]; exact h_terminal ⟨0, ic.n_pos⟩
    apply h_I_empty
    show (ic.intervalCenter ⟨0, ic.n_pos⟩).val ∈
        Set.Ioo ((ic.intervalCenter ⟨0, ic.n_pos⟩).val - ic.radius ⟨0, ic.n_pos⟩)
                ((ic.intervalCenter ⟨0, ic.n_pos⟩).val + ic.radius ⟨0, ic.n_pos⟩)
    have hr_pos := ic.radius_pos ⟨0, ic.n_pos⟩
    constructor <;> linarith
  -- Step 4: assemble FiniteCoverWithWitnesses.
  refine ⟨{
    ι := Fin L
    ιFintype := inferInstance
    nonempty := ⟨⟨0, hL_pos⟩⟩
    piece := fun k => closure (pr.J k)
    replacementEnergy := fun k => (ic.wit (pr.σ k)).replacementEnergy
    saving := fun _ => 1 / (4 * (N : ℝ))
    saving_pos := fun _ => by positivity
    saving_bound := ?_
    covers_delta_near_critical := ?_
    twoFold := ?_
    saving_ge_eps := fun _ => le_refl _ }⟩
  · -- covers_delta_near_critical: chain ic.covers + h_terminal + subset_closure.
    calc {t : unitInterval | f t ≥ m₀ - 1 / (N : ℝ)}
        ⊆ ⋃ i : Fin ic.n, ic.I i := ic.covers
      _ ⊆ ⋃ k : Fin L, pr.J k := Set.iUnion_subset h_terminal
      _ ⊆ ⋃ k : Fin L, closure (pr.J k) :=
          Set.iUnion_mono (fun _ => subset_closure)
  · -- saving_bound: use saving_bound_closure.
    intro l t ht
    exact saving_bound_closure hf pr l t ht
  · -- twoFold
    intro t
    exact terminal_twoFold pr hσ_inj t

end CombArg.Refinement
