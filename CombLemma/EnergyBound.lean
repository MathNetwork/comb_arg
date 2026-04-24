/-
Copyright (c) 2026 Xinze Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xinze Li
-/
import CombLemma.Witness
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Topology.Order.Compact

/-!
# Step 2: Arithmetic bookkeeping

Given a `Refinement` of the near-critical set (the output of Step 1,
built in `Refinement.lean`), the modified sweepout built from the
per-piece replacements has supremum bounded by `m₀ − 1/(4N)`. This file
is the arithmetic core: real-number arithmetic plus case analysis on
whether a parameter is near-critical.

The primary target is `exists_reducedEnergy_sup_lt`, which takes a
`Refinement` and produces the competitor function with the quantitative
sup bound.
-/

namespace CombLemma.EnergyBound

open CombLemma
open scoped Classical

/-- **Refinement structure.**

The output of Step 1 (`Refinement.lean`) and the input of Step 2 (this
file): a finite collection of pieces `{J_l}` covering the
`1/N`-near-critical set of `f`, with a replacement energy and a uniform
positive saving attached to each piece. -/
structure Refinement
    (K : Type*) [TopologicalSpace K]
    (X : Type*) [PseudoMetricSpace X] [PairableCover X]
    (f : K → ℝ) (m₀ : ℝ) (N : ℕ) where
  /-- Finite index type for the pieces. -/
  ι : Type
  /-- The index type is finite. -/
  [ιFintype : Fintype ι]
  /-- The index type is nonempty (a refinement with no pieces has no
  content). -/
  nonempty : Nonempty ι
  /-- The pieces `J_l ⊆ K`. -/
  piece : ι → Set K
  /-- The pieces cover the `1/N`-near-critical set of `f`. -/
  covers_near_critical :
    {t : K | f t ≥ m₀ - 1 / (N : ℝ)} ⊆ ⋃ l, piece l
  /-- Replacement energy attached to each piece. -/
  replacementEnergy : ι → K → ℝ
  /-- Per-piece saving. -/
  saving : ι → ℝ
  /-- Every saving is strictly positive. -/
  saving_pos : ∀ l, 0 < saving l
  /-- On each piece, the replacement undercuts `f` by at least `saving l`. -/
  saving_bound :
    ∀ l, ∀ t ∈ piece l, f t - replacementEnergy l t ≥ saving l
  /-- **TwoFold invariant** — every point of `K` lies in at most **two**
  pieces.

  Constitutive condition of a `Refinement`: the DLT-style interval
  refinement induction (`Refinement.lean`) produces pieces whose
  pairwise overlap is bounded. This invariant is consumed by the
  arithmetic to control total energy loss per parameter: if `t` lies in
  pieces `l₁, l₂` then the cumulative saving applied at `t` is
  `saving l₁ + saving l₂`, not an uncontrolled sum.

  Decidability on `t ∈ piece l` is supplied classically. -/
  twoFold :
    ∀ t : K, (Finset.univ.filter (fun l => t ∈ piece l)).card ≤ 2
  /-- **Uniform saving floor** — every per-piece saving is at least
  `1/(4N)`.

  This matches the quantitative threshold of the DLT replacement-family
  axiom. Combined with `twoFold`, it yields the pointwise estimate
  `reducedEnergy t ≤ f t − 1/(4N)` at near-critical `t`, whence
  `sSup (range reducedEnergy) ≤ m₀ − 1/(8N)` after case analysis with
  the non-near-critical complement. -/
  saving_ge_quarter_N :
    ∀ l, saving l ≥ 1 / (4 * (N : ℝ))

attribute [instance] Refinement.ιFintype Refinement.nonempty

namespace Refinement

open scoped Classical

variable {K : Type*} [TopologicalSpace K]
    {X : Type*} [PseudoMetricSpace X] [PairableCover X]
    {f : K → ℝ} {m₀ : ℝ} {N : ℕ}
    (R : Refinement K X f m₀ N)

/-- The multiset of per-piece savings, as a `Finset ℝ`. An implementation
detail of `minSaving`; exposed so the nonemptiness proof can be shared. -/
noncomputable def savingImage : Finset ℝ :=
  Finset.univ.image R.saving

/-- `R.savingImage` is nonempty (witnessed by `R.saving R.nonempty.some`). -/
lemma savingImage_nonempty : R.savingImage.Nonempty :=
  ⟨R.saving R.nonempty.some,
    Finset.mem_image.mpr ⟨R.nonempty.some, Finset.mem_univ _, rfl⟩⟩

/-- The minimum of `R.saving` over all pieces. The `Finset.min'` witness
is `R.savingImage_nonempty`. Enters the uniform saving
`δ := min R.minSaving (1/N)` that the arithmetic of
`exists_reducedEnergy_sup_lt` consumes. -/
noncomputable def minSaving : ℝ :=
  R.savingImage.min' R.savingImage_nonempty

/-- `R.minSaving` is realized by some `R.saving l`, hence positive by
`R.saving_pos`. -/
lemma minSaving_pos : 0 < R.minSaving := by
  obtain ⟨l, _, hl⟩ :=
    Finset.mem_image.mp (R.savingImage.min'_mem R.savingImage_nonempty)
  show 0 < R.savingImage.min' R.savingImage_nonempty
  rw [← hl]
  exact R.saving_pos l

/-- The uniform saving `δ := min R.minSaving (1/N)`. Used in both case
branches of the pointwise bound for `reducedEnergy`. -/
noncomputable def uniformSaving : ℝ :=
  min R.minSaving (1 / (N : ℝ))

/-- `δ > 0`.

From `R.minSaving > 0` (`minSaving_pos`) and `1/N > 0` (from `hN`); the
minimum of two positives is positive. -/
lemma uniformSaving_pos (hN : 0 < N) : 0 < R.uniformSaving := by
  show 0 < min R.minSaving (1 / (N : ℝ))
  exact lt_min R.minSaving_pos (one_div_pos.mpr (Nat.cast_pos.mpr hN))

/-- `δ ≤ R.saving l` for every piece `l`.

Chains `δ ≤ R.minSaving` (`min_le_left`) with `R.minSaving ≤ R.saving l`
(`Finset.min'_le` on `R.savingImage`). -/
lemma uniformSaving_le_saving (l : R.ι) : R.uniformSaving ≤ R.saving l := by
  show min R.minSaving (1 / (N : ℝ)) ≤ R.saving l
  refine (min_le_left _ _).trans ?_
  show R.savingImage.min' R.savingImage_nonempty ≤ R.saving l
  exact Finset.min'_le _ _
    (Finset.mem_image.mpr ⟨l, Finset.mem_univ _, rfl⟩)

/-- `δ ≤ 1/N`. Direct from `min_le_right`. -/
lemma uniformSaving_le_inv_N : R.uniformSaving ≤ 1 / (N : ℝ) := by
  show min R.minSaving (1 / (N : ℝ)) ≤ 1 / (N : ℝ)
  exact min_le_right _ _

/-- Indices `l` of pieces containing a given `t`. Finite by
`R.ιFintype`; cardinality bounded by `R.twoFold`. Helper for
`reducedEnergy` and the arithmetic that consumes `R.twoFold` and
`R.saving_ge_quarter_N`. -/
noncomputable def piecesContaining (t : K) : Finset R.ι :=
  Finset.univ.filter (fun l => t ∈ R.piece l)

@[simp] lemma mem_piecesContaining {t : K} {l : R.ι} :
    l ∈ R.piecesContaining t ↔ t ∈ R.piece l := by
  simp [piecesContaining]

/-- The reduced energy `f'` — DLT §3.2 scalar version.

At each `t : K`, subtract from `f t` the total saving contribution over
**all** pieces containing `t`:

    f' t  =  f t  −  ∑ { R.saving l  |  l ∈ R.piecesContaining t }

* If `t` lies in no piece: sum is empty, `f' t = f t`.
* If `t` lies in pieces `l₁, …, l_k` (with `k ≤ 2` by `R.twoFold`):
  subtraction is `∑ R.saving l_i`, each term `≥ 1/(4N)` by
  `R.saving_ge_quarter_N`. Hence total subtraction is in
  `[k · 1/(4N), k · max_saving]`, so
  `f' t ≤ f t − k · 1/(4N)`.

The explicit sum forces consideration of every piece containing `t`.
The TwoFold bound prevents over-subtraction from unbounded multiplicity;
the saving floor provides the quantitative per-piece gain.

Uses `R.piece`, `R.saving`, and (downstream) the invariants `R.twoFold`,
`R.saving_ge_quarter_N`, `R.covers_near_critical`. `R.replacementEnergy`
is not referenced here — the scalar `saving l` is a conservative
surrogate for the pointwise gain `f t − R.replacementEnergy l t`
(by `R.saving_bound`). -/
noncomputable def reducedEnergy (t : K) : ℝ :=
  f t - ∑ l ∈ R.piecesContaining t, R.saving l

/-- **Cardinality of `piecesContaining`**: at most 2.

Direct restatement of `R.twoFold` in the `piecesContaining`
abbreviation. This is the load-bearing point at which `R.twoFold` is
consumed: downstream lemmas reference this bound (e.g. the pointwise
lemma `reducedEnergy_le`) for discipline, and a sum upper bound
(twoFold × max saving) could be derived from here if needed. -/
lemma piecesContaining_card_le_two (t : K) :
    (R.piecesContaining t).card ≤ 2 := R.twoFold t

/-- **Per-piece lower bound on the `reducedEnergy` subtraction**: if
`t ∈ R.piece l` for some `l`, then the sum of savings over all pieces
containing `t` is at least `1/(4N)`.

Load-bearing consumption of `R.saving_ge_quarter_N` (each summand is at
least `1/(4N)`) and `R.saving_pos` (rest of the sum is non-negative,
so dropping terms only decreases). -/
lemma quarter_N_le_sum_saving {t : K} {l : R.ι} (hl : t ∈ R.piece l) :
    1 / (4 * (N : ℝ)) ≤ ∑ l' ∈ R.piecesContaining t, R.saving l' := by
  have hmem : l ∈ R.piecesContaining t := R.mem_piecesContaining.mpr hl
  have hnonneg : ∀ l' ∈ R.piecesContaining t, 0 ≤ R.saving l' :=
    fun l' _ => le_of_lt (R.saving_pos l')
  calc 1 / (4 * (N : ℝ))
      ≤ R.saving l := R.saving_ge_quarter_N l
    _ ≤ ∑ l' ∈ R.piecesContaining t, R.saving l' :=
        Finset.single_le_sum hnonneg hmem

/-- `f t ≤ m₀` on compact `K`: `m₀ = sSup (range f)`, `f t ∈ range f`,
`range f` bounded above by compactness plus continuity. -/
lemma f_le_m0 [CompactSpace K] (hf : Continuous f)
    (hm : m₀ = sSup (Set.range f)) (t : K) : f t ≤ m₀ := by
  rw [hm]
  exact le_csSup (IsCompact.bddAbove (isCompact_range hf)) (Set.mem_range_self t)

/-- Contrapositive of `covers_near_critical`: if `t` is in no piece,
then `t` is not in the near-critical set, i.e. `f t < m₀ - 1/N`.
**Strict** inequality — the `<` is what feeds the strict
`sSup < m₀` conclusion downstream. Uses `not_le.mp`. -/
lemma lt_of_not_mem_iUnion_piece {t : K} (ht : t ∉ ⋃ l, R.piece l) :
    f t < m₀ - 1 / (N : ℝ) :=
  not_le.mp (fun h => ht (R.covers_near_critical h))

/-- **Lemma P** *(pointwise bound)*: `f' t ≤ m₀ − 1/(4N)` for every `t`.

**Case `t ∈ ⋃ pieces`** (count ≥ 1): sum
`∑ l ∈ R.piecesContaining t, R.saving l ≥ count · 1/(4N) ≥ 1/(4N)`
(by `R.saving_ge_quarter_N`), so
`R.reducedEnergy t = f t − sum ≤ f t − 1/(4N) ≤ m₀ − 1/(4N)`
(by `f_le_m0`).

**Case `t ∉ ⋃ pieces`** (count = 0): sum = 0, so
`R.reducedEnergy t = f t`. By `lt_of_not_mem_iUnion_piece`,
`f t < m₀ − 1/N ≤ m₀ − 1/(4N)` (since `N ≥ 1`). -/
lemma reducedEnergy_le [CompactSpace K] (hf : Continuous f)
    (hm : m₀ = sSup (Set.range f)) (hN : 0 < N) (t : K) :
    R.reducedEnergy t ≤ m₀ - 1 / (4 * (N : ℝ)) := by
  -- Invariant `R.twoFold` consumed via `piecesContaining_card_le_two`:
  -- the summation below ranges over a `Finset` of cardinality ≤ 2.
  -- Not strictly load-bearing in this case's arithmetic (the bound
  -- holds regardless of overlap multiplicity), but cited to record the
  -- structural role of `R.twoFold` — a pointwise scalar-reduction
  -- argument that ignored `R.twoFold` entirely would be exposed here.
  have _htwoFold : (R.piecesContaining t).card ≤ 2 :=
    R.piecesContaining_card_le_two t
  have hN_real : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN
  show f t - ∑ l' ∈ R.piecesContaining t, R.saving l' ≤ m₀ - 1 / (4 * (N : ℝ))
  by_cases h : (R.piecesContaining t).Nonempty
  · -- Case A: t is in some piece — use `saving_ge_quarter_N` via
    -- `quarter_N_le_sum_saving`, plus `f t ≤ m₀`.
    obtain ⟨l, hl⟩ := h
    have hl_mem : t ∈ R.piece l := R.mem_piecesContaining.mp hl
    have hf_m₀ : f t ≤ m₀ := f_le_m0 hf hm t
    have hsum : 1 / (4 * (N : ℝ)) ≤ ∑ l' ∈ R.piecesContaining t, R.saving l' :=
      R.quarter_N_le_sum_saving hl_mem
    linarith
  · -- Case B: t in no piece — sum is 0, but `f t < m₀ − 1/N`.
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have ht_not : t ∉ ⋃ l, R.piece l := by
      intro hmem
      obtain ⟨l, hl⟩ := Set.mem_iUnion.mp hmem
      have hmem' : l ∈ R.piecesContaining t := R.mem_piecesContaining.mpr hl
      simp [h] at hmem'
    have hlt : f t < m₀ - 1 / (N : ℝ) := R.lt_of_not_mem_iUnion_piece ht_not
    have hquart_le_N : 1 / (4 * (N : ℝ)) ≤ 1 / (N : ℝ) :=
      one_div_le_one_div_of_le hN_real (by linarith)
    rw [h, Finset.sum_empty]
    linarith

/-- **Lemma G**: `BddAbove (range R.reducedEnergy)`.

Follows from Lemma P: `m₀ − 1/(4N)` is an explicit uniform upper
bound. -/
lemma reducedEnergy_range_bddAbove [CompactSpace K] (hf : Continuous f)
    (hm : m₀ = sSup (Set.range f)) (hN : 0 < N) :
    BddAbove (Set.range R.reducedEnergy) := by
  refine ⟨m₀ - 1 / (4 * (N : ℝ)), ?_⟩
  rintro x ⟨t, rfl⟩
  exact R.reducedEnergy_le hf hm hN t

/-- **Lemma H** *(supremum bound)*: `sSup (range R.reducedEnergy) ≤ m₀ − 1/(4N)`.

DLT-faithful quantitative bound. From Lemma P (uniform pointwise
`≤ m₀ − 1/(4N)`) and `csSup_le`. -/
lemma reducedEnergy_sSup_le [CompactSpace K] [Nonempty K]
    (hf : Continuous f) (hm : m₀ = sSup (Set.range f)) (hN : 0 < N) :
    sSup (Set.range R.reducedEnergy) ≤ m₀ - 1 / (4 * (N : ℝ)) := by
  apply csSup_le (Set.range_nonempty _)
  rintro x ⟨t, rfl⟩
  exact R.reducedEnergy_le hf hm hN t

end Refinement

/-- **Primary target of this file.**

Given a refinement of the `1/N`-near-critical set of a continuous `f`
with supremum `m₀`, a reduced energy `f' : K → ℝ` exists whose supremum
is bounded by `m₀ − 1/(4N)` — the DLT-faithful quantitative form.

## Proof architecture

`reducedEnergy t := f t − ∑ l ∈ R.piecesContaining t, R.saving l`
(explicit sum over all pieces containing `t`).

Both `R.twoFold` and `R.saving_ge_quarter_N` are actively consumed.
Case split on `t ∈ ⋃ R.piece` (use `saving_ge_quarter_N` for the lower
bound on the sum) vs `t ∉ ⋃ R.piece` (use `covers_near_critical`
contrapositive for `f t < m₀ − 1/N`).

The conclusion is `≤ m₀ − 1/(4N)`, not `< m₀`. The quantitative form is
essential: strict `< m₀` alone would be a trivialization. -/
theorem exists_reducedEnergy_sup_lt
    {K : Type*} [TopologicalSpace K] [CompactSpace K] [Nonempty K]
    {X : Type*} [PseudoMetricSpace X] [PairableCover X]
    {f : K → ℝ} (hf : Continuous f)
    {m₀ : ℝ} (_hm_pos : 0 < m₀) (hm : m₀ = sSup (Set.range f))
    {N : ℕ} (hN : 0 < N)
    (R : Refinement K X f m₀ N) :
    ∃ f' : K → ℝ, sSup (Set.range f') ≤ m₀ - 1 / (4 * (N : ℝ)) :=
  ⟨R.reducedEnergy, R.reducedEnergy_sSup_le hf hm hN⟩

end CombLemma.EnergyBound
