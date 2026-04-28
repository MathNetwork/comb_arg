/-
Copyright (c) 2026 Xinze Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xinze Li
-/
import CombArg.OneDim.CoverConstruction
import CombArg.OneDim.Induction
import CombArg.OneDim.DLTCover

/-!
# Combinatorial main theorem: Assembly

This file packages the 1D cover-construction infrastructure into the
library's combinatorial main theorems:

* `exists_DLTCover` — the **structured** output. Chains
  `exists_initialCover` (Stage A) and `exists_terminal_refinement`
  (Stage B) into a `DLTCover`, exposing the spacing / partial
  refinement / σ-injectivity data for downstream geometric
  consumers.
* `exists_refinement` — the **abstract scalar** output, defined as
  `(exists_DLTCover ...).toFinite`. Same signature as v0.3 (returns
  `FiniteCoverWithWitnesses`); existing consumers
  (`CombArg.exists_sup_reduction`, etc.) are unchanged.

The split mirrors the design distinction recorded in
`paper/sections/intro.tex` Remark 1.5: the construction is a
first-class object of the formalization, not just a means to the
scalar conclusion.
-/

namespace CombArg.OneDim

open CombArg
open scoped Classical

variable {f : unitInterval → ℝ} {m₀ : ℝ} {N : ℕ}

/-! ## Structured output: `exists_DLTCover` -/

/-- **DLT-style construction, structured form.** From the witness
hypothesis on `unitInterval`, builds a `DLTCover` carrying the full
Stage A + B intermediate state: `InitialCover` with spacing (a)+(b),
terminal `PartialRefinement`, σ-injectivity, and the termination
invariant `∀ i, ic.I i ⊆ ⋃ k, pr.J k`.

This is the **structured** output of the DLT §3.2 Step 1
construction; downstream geometric consumers (modified-sweepout
blending) read off the spacing / overlap / witness-assignment data
they need from this object directly.

For the abstract scalar API (`FiniteCoverWithWitnesses`) use
`exists_refinement` below, which is just this output downgraded via
`DLTCover.toFinite`. -/
lemma exists_DLTCover
    (hf : Continuous f)
    (hm : m₀ = sSup (Set.range f))
    (hN : 0 < N)
    (witness : ∀ t : unitInterval, f t ≥ m₀ - 1 / (N : ℝ) →
                 LocalWitness unitInterval f t (1 / (4 * (N : ℝ)))) :
    Nonempty (DLTCover f m₀ N) := by
  -- Stage A: initial cover.
  obtain ⟨ic⟩ := exists_initialCover hf hm hN witness
  -- Stage B: iterate to terminal state.
  obtain ⟨L, pr, hσ_inj, h_terminal⟩ := exists_terminal_refinement ic
  -- L ≥ 1 (else ic.I ⟨0, ic.n_pos⟩ ⊆ ∅, contradicting nonemptiness).
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
  exact ⟨{
    initialCover := ic
    L := L
    L_pos := hL_pos
    refinement := pr
    σ_injective := hσ_inj
    initialCover_covered := h_terminal }⟩

/-! ## Abstract scalar output: `exists_refinement` -/

/-- **Combinatorial main theorem** (combinatorial core of
Almgren--Pitts for a 1D sweepout), abstract scalar form.

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

Defined as the composition `exists_DLTCover ∘ DLTCover.toFinite`.
The signature (and behavior on consumers) is identical to v0.3:
the only change is internal — the output is now produced by
downgrading the structured `DLTCover` rather than packaged
inline.

The existence of a scalar sup-reducing competitor `f'` follows as
a three-line bookkeeping corollary
(`CombArg.exists_sup_reduction_of_cover`,
`CombArg.exists_sup_reduction`); the non-trivial content is the
construction packaged in `exists_DLTCover`. An alternative,
strictly shorter proof of this scalar theorem (which discards the
DLT structure and is therefore unsuitable for geometric lift) is
available in `CombArg.Scalar.Partition`; see
`paper/sections/intro.tex` Remark 1.5 for the design rationale. -/
lemma exists_refinement
    (hf : Continuous f)
    (hm : m₀ = sSup (Set.range f))
    (hN : 0 < N)
    (witness : ∀ t : unitInterval, f t ≥ m₀ - 1 / (N : ℝ) →
                 LocalWitness unitInterval f t (1 / (4 * (N : ℝ)))) :
    Nonempty (FiniteCoverWithWitnesses unitInterval f m₀
              (1 / (N : ℝ)) (1 / (4 * (N : ℝ)))) := by
  obtain ⟨D⟩ := exists_DLTCover hf hm hN witness
  exact ⟨D.toFinite hf hN⟩

end CombArg.OneDim
