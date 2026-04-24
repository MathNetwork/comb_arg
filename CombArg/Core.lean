/-
Copyright (c) 2026 Xinze Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xinze Li
-/
import Mathlib.Data.Fintype.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact

/-!
# Core — sup-reduction bookkeeping (corollary layer)

Given a `FiniteCoverWithWitnesses` of the `δ`-near-critical set
`{t | f t ≥ m₀ − δ}` with per-piece savings at least `ε > 0`
(`ε ≤ δ`) and multiplicity at most 2, this file derives a scalar
competitor `f' : K → ℝ` with `sSup (range f') ≤ m₀ − ε`.

This is the **bookkeeping corollary** of the combinatorial main
theorem `CombArg.Refinement.exists_refinement`, stripped of any
parameter-space specifics (`unitInterval`, 1D covering,
`LocalWitness`, `PairableCover`) and uniform in `(δ, ε)`.
Consumers with an application-specific cover construction feed it
in; this file handles the scalar arithmetic only.

See `CombArg/SupReduction.lean` for the 1D application (`K = [0,1]`,
`δ = 1/N`, `ε = 1/(4N)`) that composes the 1D cover construction
(`CombArg/Refinement/`) with this corollary.
-/

namespace CombArg

open scoped Classical

/-- **Scalar sup reduction lemma** — the pure-arithmetic core.

If `g : K → ℝ` is pointwise dominated by `f` and saves at least
`ε` on the super-level set `{f ≥ m₀ − δ}`, and `ε ≤ δ`, then
`sSup (range g) ≤ m₀ − ε`. No topology, no compactness, no cover:
the content is the single case split on whether `t` belongs to
the super-level set.

This lemma is independent of the combinatorial-argument
structure; it packages the single arithmetic fact that the rest
of `CombArg.Core` composes with the cover-and-witness data. -/
lemma sup_le_of_saving {K : Type*} [Nonempty K] {f g : K → ℝ}
    {m₀ δ ε : ℝ}
    (hm : m₀ = sSup (Set.range f))
    (hbdd : BddAbove (Set.range f))
    (hle : ε ≤ δ)
    (hg_le : ∀ t, g t ≤ f t)
    (h_sav : ∀ t, f t ≥ m₀ - δ → f t - g t ≥ ε) :
    sSup (Set.range g) ≤ m₀ - ε := by
  apply csSup_le (Set.range_nonempty _)
  rintro y ⟨t, rfl⟩
  have hft : f t ≤ m₀ := by
    rw [hm]
    exact le_csSup hbdd (Set.mem_range_self t)
  by_cases h : f t ≥ m₀ - δ
  · have := h_sav t h
    linarith
  · have hlt : f t < m₀ - δ := lt_of_not_ge h
    have := hg_le t
    linarith

/-- **Finite cover with witnesses.**

The abstract input to the core theorem: a finite index type `ι` of
pieces `{piece l ⊆ K}` covering the `δ`-near-critical set
`{t | f t ≥ m₀ − δ}`, with per-piece replacement-energy functions,
per-piece savings bounded below by `ε`, and multiplicity ≤ 2.

Parameterized by the near-critical threshold `δ` and the per-piece
saving floor `ε`. For the 1D application (`CombArg/Refinement/`),
`δ = 1/N` and `ε = 1/(4N)`.

The multiplicity bound is currently hardcoded to `2`, matching the
DLT parity-rescue construction. It is recorded as a structural
invariant but is **not arithmetically load-bearing** for the output
`m₀ − ε`: the pointwise bound uses only `saving_ge_eps` and
`saving_pos`. -/
structure FiniteCoverWithWitnesses
    (K : Type*) [TopologicalSpace K]
    (f : K → ℝ) (m₀ δ ε : ℝ) where
  /-- Finite index type for the pieces. -/
  ι : Type
  /-- The index type is finite. -/
  [ιFintype : Fintype ι]
  /-- The index type is nonempty (a cover with no pieces has no content). -/
  nonempty : Nonempty ι
  /-- The pieces `piece l ⊆ K`. -/
  piece : ι → Set K
  /-- The pieces cover the `δ`-near-critical set of `f`. -/
  covers_delta_near_critical :
    {t : K | f t ≥ m₀ - δ} ⊆ ⋃ l, piece l
  /-- Replacement-energy function attached to each piece. -/
  replacementEnergy : ι → K → ℝ
  /-- Per-piece scalar saving. -/
  saving : ι → ℝ
  /-- Every saving is strictly positive. -/
  saving_pos : ∀ l, 0 < saving l
  /-- On each piece, the replacement undercuts `f` by at least `saving l`. -/
  saving_bound :
    ∀ l, ∀ t ∈ piece l, f t - replacementEnergy l t ≥ saving l
  /-- **Multiplicity bound.** Every point of `K` lies in at most two
  pieces. Structural invariant of the DLT-style cover; not consumed
  by the scalar arithmetic of the core theorem. -/
  twoFold :
    ∀ t : K, (Finset.univ.filter (fun l => t ∈ piece l)).card ≤ 2
  /-- **Per-piece saving floor** — each saving is at least `ε`. -/
  saving_ge_eps : ∀ l, saving l ≥ ε

attribute [instance] FiniteCoverWithWitnesses.ιFintype
attribute [instance] FiniteCoverWithWitnesses.nonempty

namespace FiniteCoverWithWitnesses

open scoped Classical

variable {K : Type*} [TopologicalSpace K]
    {f : K → ℝ} {m₀ δ ε : ℝ}
    (C : FiniteCoverWithWitnesses K f m₀ δ ε)

/-- Indices of pieces containing a given `t`. Finite by `C.ιFintype`;
cardinality bounded by `C.twoFold`. -/
noncomputable def piecesContaining (t : K) : Finset C.ι :=
  Finset.univ.filter (fun l => t ∈ C.piece l)

@[simp] lemma mem_piecesContaining {t : K} {l : C.ι} :
    l ∈ C.piecesContaining t ↔ t ∈ C.piece l := by
  simp [piecesContaining]

/-- **The reduced energy** — DLT §3.2 scalar version.

At each `t : K`, subtract from `f t` the total saving contribution
over all pieces containing `t`:

    f' t  =  f t  −  ∑ { C.saving l | l ∈ C.piecesContaining t }.

* If `t` lies in no piece: sum is empty, `f' t = f t`.
* If `t` lies in at least one piece: each summand is `≥ ε` by
  `saving_ge_eps`, the rest are non-negative by `saving_pos`, so the
  total subtraction is `≥ ε`.

The explicit sum makes the multiplicity contribution transparent.
The two-fold bound `C.twoFold` prevents unbounded over-subtraction
but is not needed for the current output bound. -/
noncomputable def reducedEnergy (t : K) : ℝ :=
  f t - ∑ l ∈ C.piecesContaining t, C.saving l

/-- **Cardinality of `piecesContaining`**: at most 2. Direct
restatement of `C.twoFold` in the `piecesContaining` abbreviation. -/
lemma piecesContaining_card_le_two (t : K) :
    (C.piecesContaining t).card ≤ 2 := C.twoFold t

/-- **Per-piece lower bound on the `reducedEnergy` subtraction**:
if `t ∈ C.piece l` for some `l`, then the sum of savings over all
pieces containing `t` is at least `ε`.

Load-bearing consumption of `saving_ge_eps` (one summand `≥ ε`)
combined with `saving_pos` (other summands non-negative). -/
lemma eps_le_sum_saving {t : K} {l : C.ι} (hl : t ∈ C.piece l) :
    ε ≤ ∑ l' ∈ C.piecesContaining t, C.saving l' := by
  have hmem : l ∈ C.piecesContaining t := C.mem_piecesContaining.mpr hl
  have hnonneg : ∀ l' ∈ C.piecesContaining t, 0 ≤ C.saving l' :=
    fun l' _ => le_of_lt (C.saving_pos l')
  calc ε
      ≤ C.saving l := C.saving_ge_eps l
    _ ≤ ∑ l' ∈ C.piecesContaining t, C.saving l' :=
        Finset.single_le_sum hnonneg hmem

/-- `f t ≤ m₀` on compact `K`: `m₀ = sSup (range f)`, `f t ∈ range f`,
`range f` bounded above by compactness plus continuity. -/
lemma f_le_m0 [CompactSpace K] (hf : Continuous f)
    (hm : m₀ = sSup (Set.range f)) (t : K) : f t ≤ m₀ := by
  rw [hm]
  exact le_csSup (IsCompact.bddAbove (isCompact_range hf)) (Set.mem_range_self t)

/-- Contrapositive of `covers_delta_near_critical`: if `t` is in no
piece, then `t` is not in the `δ`-near-critical set, i.e.
`f t < m₀ − δ`. -/
lemma lt_of_not_mem_iUnion_piece {t : K} (ht : t ∉ ⋃ l, C.piece l) :
    f t < m₀ - δ :=
  not_le.mp (fun h => ht (C.covers_delta_near_critical h))

/-- **Pointwise bound**: `reducedEnergy t ≤ m₀ − ε` for every `t`.

* **Case `t ∈ ⋃ pieces`** (count ≥ 1): sum `≥ ε` by
  `eps_le_sum_saving`, so `reducedEnergy t = f t − sum ≤ f t − ε
  ≤ m₀ − ε` (using `f_le_m0`).
* **Case `t ∉ ⋃ pieces`** (count = 0): sum = 0, so
  `reducedEnergy t = f t`. By `lt_of_not_mem_iUnion_piece`,
  `f t < m₀ − δ ≤ m₀ − ε` (using `ε ≤ δ`). -/
lemma reducedEnergy_le [CompactSpace K] (hf : Continuous f)
    (hm : m₀ = sSup (Set.range f)) (hle : ε ≤ δ) (t : K) :
    C.reducedEnergy t ≤ m₀ - ε := by
  show f t - ∑ l' ∈ C.piecesContaining t, C.saving l' ≤ m₀ - ε
  by_cases h : (C.piecesContaining t).Nonempty
  · obtain ⟨l, hl⟩ := h
    have hl_mem : t ∈ C.piece l := C.mem_piecesContaining.mp hl
    have hf_m₀ : f t ≤ m₀ := f_le_m0 hf hm t
    have hsum : ε ≤ ∑ l' ∈ C.piecesContaining t, C.saving l' :=
      C.eps_le_sum_saving hl_mem
    linarith
  · rw [Finset.not_nonempty_iff_eq_empty] at h
    have ht_not : t ∉ ⋃ l, C.piece l := by
      intro hmem
      obtain ⟨l, hl⟩ := Set.mem_iUnion.mp hmem
      have hmem' : l ∈ C.piecesContaining t := C.mem_piecesContaining.mpr hl
      simp [h] at hmem'
    have hlt : f t < m₀ - δ := C.lt_of_not_mem_iUnion_piece ht_not
    rw [h, Finset.sum_empty]
    linarith

/-- **`range C.reducedEnergy` is bounded above**. Follows from
`reducedEnergy_le`: `m₀ − ε` is an explicit uniform upper bound. -/
lemma reducedEnergy_range_bddAbove [CompactSpace K] (hf : Continuous f)
    (hm : m₀ = sSup (Set.range f)) (hle : ε ≤ δ) :
    BddAbove (Set.range C.reducedEnergy) := by
  refine ⟨m₀ - ε, ?_⟩
  rintro x ⟨t, rfl⟩
  exact C.reducedEnergy_le hf hm hle t

/-- **Supremum bound**: `sSup (range C.reducedEnergy) ≤ m₀ − ε`.

Proved by reducing to the generic `sup_le_of_saving` lemma: the
reduced energy is pointwise dominated by `f` (savings are positive,
so their sum is non-negative), and on the `δ`-super-level set the
sum of savings is bounded below by `ε` (a piece containing `t` has
saving `≥ ε`, remaining savings are non-negative). -/
lemma reducedEnergy_sSup_le [CompactSpace K] [Nonempty K]
    (hf : Continuous f) (hm : m₀ = sSup (Set.range f)) (hle : ε ≤ δ) :
    sSup (Set.range C.reducedEnergy) ≤ m₀ - ε := by
  refine sup_le_of_saving hm
    (IsCompact.bddAbove (isCompact_range hf)) hle ?hg_le ?h_sav
  case hg_le =>
    intro t
    show f t - ∑ l ∈ C.piecesContaining t, C.saving l ≤ f t
    have hnonneg : (0 : ℝ) ≤ ∑ l ∈ C.piecesContaining t, C.saving l :=
      Finset.sum_nonneg fun l _ => le_of_lt (C.saving_pos l)
    linarith
  case h_sav =>
    intro t ht
    show f t - (f t - ∑ l ∈ C.piecesContaining t, C.saving l) ≥ ε
    have htu : t ∈ ⋃ l, C.piece l := C.covers_delta_near_critical ht
    obtain ⟨l, hl⟩ := Set.mem_iUnion.mp htu
    have hbound : ε ≤ ∑ l' ∈ C.piecesContaining t, C.saving l' :=
      C.eps_le_sum_saving hl
    linarith

end FiniteCoverWithWitnesses

/-- **Corollary: sup reduction bookkeeping** — scalar competitor
existence from a `FiniteCoverWithWitnesses`, generic `K`.

This is a corollary of the combinatorial main theorem
`CombArg.Refinement.exists_refinement` (which produces such a
cover on the 1D case); the present declaration discharges the
arithmetic bookkeeping that turns any such cover into a
sup-reducing competitor, in a form that is independent of the
1D cover-construction and applies to any compact `K`.

Let `K` be a compact nonempty space, `f : K → ℝ` continuous with
`m₀ = sSup (range f)`, and fix `0 < ε ≤ δ`. From a
`FiniteCoverWithWitnesses K f m₀ δ ε` (a finite multiplicity-bounded
cover of the `δ`-near-critical set with per-piece savings ≥ ε), a
competitor `f' : K → ℝ` exists with `sSup (range f') ≤ m₀ − ε`.

The output `f' = C.reducedEnergy` is the DLT-style pointwise
subtraction of all applicable savings from `f`. -/
theorem exists_sup_reduction_of_cover
    {K : Type*} [TopologicalSpace K] [CompactSpace K] [Nonempty K]
    {f : K → ℝ} (hf : Continuous f)
    {m₀ : ℝ} (hm : m₀ = sSup (Set.range f))
    {δ ε : ℝ} (_hδ : 0 < δ) (_hε : 0 < ε) (hle : ε ≤ δ)
    (C : FiniteCoverWithWitnesses K f m₀ δ ε) :
    ∃ f' : K → ℝ, sSup (Set.range f') ≤ m₀ - ε :=
  ⟨C.reducedEnergy, C.reducedEnergy_sSup_le hf hm hle⟩

end CombArg
