# Project overview

**Date:** 2026-04-25
**Status:** Zero `sorry` across all modules. v0.2 API simplification
applied (PairableCover removed, witness shape simplified, unused
hypotheses dropped). Only the three standard Lean 4 / Mathlib
foundational axioms (`propext`, `Classical.choice`, `Quot.sound`)
transitively used; verified via `test/Smoke.lean`.

## Goal

Machine-verified, sorry-free formalization of the combinatorial core
of De Lellis–Tasnady (2013) §3.2 — the cover-refinement step
(Step 1) plus its scalar sup-reduction consequence (Step 2) —
factored as a self-contained metric-combinatorial theorem
independent of any geometric-measure-theory content.

## Public theorems

The library exports two theorems (plus a one-parameter chained
corollary).

### Combinatorial main theorem — `exists_refinement`

[`CombArg/OneDim/Assembly.lean`](../CombArg/OneDim/Assembly.lean):

```lean
lemma exists_refinement
    {f : unitInterval → ℝ} (hf : Continuous f)
    (hm : m₀ = sSup (Set.range f))
    (hN : 0 < N)
    (witness : ∀ t : unitInterval, f t ≥ m₀ - 1 / (N : ℝ) →
                 LocalWitness unitInterval f t (1 / (4 * (N : ℝ)))) :
    Nonempty (FiniteCoverWithWitnesses unitInterval f m₀
              (1 / (N : ℝ)) (1 / (4 * (N : ℝ))))
```

Given a `LocalWitness` family on the near-critical set of
`f : unitInterval → ℝ`, produce a `FiniteCoverWithWitnesses` with
two-fold overlap and uniform per-piece saving `1/(4N)`. This is
the non-trivial content extracted from the Almgren–Pitts
combinatorial argument (Lebesgue-number cover, bounded
smallest-index refinement, parity-rescue two-fold invariant).

### Sup-reduction bookkeeping corollary — `exists_sup_reduction_of_cover`

[`CombArg/Cover.lean`](../CombArg/Cover.lean):

```lean
theorem exists_sup_reduction_of_cover
    {K : Type*} [TopologicalSpace K] [CompactSpace K] [Nonempty K]
    {f : K → ℝ} (hf : Continuous f)
    {m₀ : ℝ} (hm : m₀ = sSup (Set.range f))
    {δ ε : ℝ} (hle : ε ≤ δ)
    (C : FiniteCoverWithWitnesses K f m₀ δ ε) :
    ∃ f' : K → ℝ,
      (∀ t, f' t ≤ f t) ∧
      (∀ t, t ∉ (⋃ l, C.piece l) → f' t = f t) ∧
      sSup (Set.range f') ≤ m₀ - ε
```

From any `FiniteCoverWithWitnesses` on a compact nonempty space
`K`, produce a competitor `f'` with pointwise dominance,
off-support agreement with `f`, and the sup bound `≤ m₀ − ε`.
Three-line scalar arithmetic; generic in `K`.

### One-parameter chained corollary — `exists_sup_reduction`

[`CombArg/SupReduction.lean`](../CombArg/SupReduction.lean):

```lean
theorem exists_sup_reduction
    {f : unitInterval → ℝ} (hf : Continuous f)
    {m₀ : ℝ} (hm : m₀ = sSup (Set.range f))
    {N : ℕ} (hN : 0 < N)
    (witness : ∀ t : unitInterval, f t ≥ m₀ - 1 / (N : ℝ) →
                  LocalWitness unitInterval f t (1 / (4 * (N : ℝ)))) :
    ∃ (f' : unitInterval → ℝ) (S : Set unitInterval),
      {t : unitInterval | f t ≥ m₀ - 1 / (N : ℝ)} ⊆ S ∧
      (∀ t, f' t ≤ f t) ∧
      (∀ t, t ∉ S → f' t = f t) ∧
      sSup (Set.range f') ≤ m₀ - 1 / (4 * (N : ℝ))
```

The 1D specialization: chain `exists_refinement` through
`exists_sup_reduction_of_cover` on `K = unitInterval` with
`(δ, ε) = (1/N, 1/(4N))`.

**Reading the hypotheses (DLT §3.2 correspondence)**:

* `f` — the scalar energy (paper's `E` on a one-parameter sweepout).
* `hm : m₀ = sSup (range f)` — `m₀` is the sup of `f`. The
  corresponding min-max interpretation (as infimum over admissible
  classes) is an external framing the client supplies; see
  [`design-notes.md §2`](design-notes.md) for the reduction-form
  rationale.
* `N : ℕ` with `hN : 0 < N` — the near-criticality parameter; the
  output bound is `1/(4N)` quantitative.
* `witness` — paper's Lemma 3.1 output (existence of a replacement
  family): at every near-critical parameter, a `LocalWitness` with
  saving **exactly `1/(4N)`**. See
  [`design-notes.md §9`](design-notes.md) for the commitment to
  `1/(4N)` over the weaker `∃ ε > 0` form.

## Proof architecture

### Combinatorial main theorem (`exists_refinement`)

A three-stage construction.

* **Stage A** (`exists_initialCover` in
  [`CombArg/OneDim/CoverConstruction.lean`](../CombArg/OneDim/CoverConstruction.lean)):
  from the witness hypothesis plus `nearCritical` compactness,
  build an `InitialCover` — a family of intervals
  `I_i = (intervalCenter i − radius i, intervalCenter i + radius i)`
  satisfying DLT's spacing condition (a)
  (`intervalCenter i + radius i < intervalCenter (i+2) − radius (i+2)`)
  and covering the near-critical set. Construction: grid
  `c_k := k/M` for `M > 4/λ` (λ from Lebesgue number) plus a filter
  keeping grid points near NC; witness centers picked via Lebesgue.

* **Stage B** (`exists_terminal_refinement` in
  [`CombArg/OneDim/Induction.lean`](../CombArg/OneDim/Induction.lean)):
  iterate the DLT induction `step_zero` → `step_succ_at` × `ic.n`
  times, producing a `PartialRefinement ic L` with
  `Function.Injective pr.σ` and `∀ i, ic.I i ⊆ ⋃ pr.J k`.

* **Stage C** (`exists_refinement` assembly in
  [`CombArg/OneDim/Assembly.lean`](../CombArg/OneDim/Assembly.lean)):
  package as `FiniteCoverWithWitnesses` with
  `piece k := closure (pr.J k)`, `saving k := 1/(4N)` uniform.
  `twoFold` via `terminal_twoFold` (parity argument on even-gap
  chain disjointness); `saving_bound` via `saving_bound_closure`
  (continuity-based extension from open neighborhood to closure
  using `LocalWitness.replacementEnergy_continuous`).

### Sup-reduction bookkeeping corollary (`exists_sup_reduction_of_cover`)

Three-line scalar arithmetic, fully in
[`CombArg/Cover.lean`](../CombArg/Cover.lean):

* The competitor is `f'(t) := f(t) − ∑ {saving l | l ∈ piecesContaining t}`.
* On each piece, the sum-of-savings is `≥ ε` (`ε_le_sum_saving`),
  so `f' ≤ f − ε ≤ m₀ − ε` (`f_le_m₀`).
* Off the cover, the sum is `0`, so `f' = f` and the
  near-critical complement gives `f t < m₀ − δ ≤ m₀ − ε`.

The argument is uniform in the multiplicity bound and per-piece
saving floor; `twoFold` is recorded as a structural invariant of
the cover but is not consumed in the bookkeeping arithmetic.

## Definition tour

### [`CombArg/Witness.lean`](../CombArg/Witness.lean)

* `LocalWitness K f t ε` — open neighborhood of `t`, continuous
  replacement-energy function on `K`, and saving bound
  `f s − replacementEnergy s ≥ ε` on the neighborhood. The
  replacement is represented by its energy only, not by a concrete
  family `K → X`, keeping the theorem agnostic to how the
  replacement is realized geometrically.

### [`CombArg/Cover.lean`](../CombArg/Cover.lean)

* `FiniteCoverWithWitnesses K f m₀ δ ε` — finite multiplicity-bounded
  cover of the `δ`-near-critical set, with per-piece replacement
  energies and savings bounded below by `ε`.
* `FiniteCoverWithWitnesses.reducedEnergy` — the scalar `f'` via
  `f − Σ saving` over `piecesContaining`.
* `csSup_range_le_of_pointwise_saving` — the pure-arithmetic core.
* `exists_sup_reduction_of_cover` — the bookkeeping theorem.

### [`CombArg/OneDim/SpacedIntervals.lean`](../CombArg/OneDim/SpacedIntervals.lean)

* `openInterval c r` — the canonical
  `Subtype.val ⁻¹' Set.Ioo (c.val - r) (c.val + r)` shape on
  `unitInterval`.
* `SkippedSpacedIntervals` — geometric structure of skip-2 spaced
  open intervals on `unitInterval`, carrying the spacing and
  parity-rescue lemmas (`chain_spacing`, `disjoint_of_even_gap`,
  `closure_disjoint_of_even_gap`, `not_three_overlap`,
  `not_three_overlap_any_order`).

### [`CombArg/OneDim/InitialCover.lean`](../CombArg/OneDim/InitialCover.lean)

* `nearCritical` and its closedness / compactness / nonemptiness.
* `InitialCover` — DLT's `{I_i}` family with `intervalCenter`,
  `radius`, `witnessCenter` fields (split per
  [`design-notes.md §10`](design-notes.md)),
  `two_fold_spacing`, `I_subset_neighborhood`, `covers`.
* `InitialCover.toSkippedSpacedIntervals` — geometric projection
  to `SkippedSpacedIntervals` (delegation point for the
  disjointness lemmas).

### [`CombArg/OneDim/Induction.lean`](../CombArg/OneDim/Induction.lean)

* `ExtendResult` — bundled output of one inductive step: extended
  `PartialRefinement` plus the four invariants (`J_castSucc`,
  `σ_castSucc`, `σ_last`, `covers_i_star`) needed by termination.
* `step_succ_at` — DLT §3.2 Step 1's two-case dispatch on
  `ic.I i_star ⊆ pr.J prev ∪ ic.I (pr.σ prev)`.
* `exists_terminal_refinement` — bounded iteration on
  `remaining.card`. The paper's smallest-index choice
  (`Finset.min'`) lives in this file's iteration control flow.

### [`CombArg/OneDim/Assembly.lean`](../CombArg/OneDim/Assembly.lean)

* `terminal_twoFold` — TwoFold via parity rescue + σ-injectivity.
* `saving_bound_closure` — saving-bound extension from `J k` to
  `closure (J k)` via continuity.
* `exists_refinement` — assembly into `FiniteCoverWithWitnesses`.

## Axiom dependencies

Verified via `test/Smoke.lean`'s `#print axioms` block; all three
public theorems print

```
depends on axioms: [propext, Classical.choice, Quot.sound]
```

— the three standard Lean 4 / Mathlib foundational axioms. No
custom axioms are declared anywhere in the library.

## Findings surfaced by formalization

Paper-level findings the formalization process surfaced that the
DLT argument compresses:

1. **Witness threshold is quantitative, not existential.** The
   hypothesis must commit to `ε = 1/(4N)` exactly, not
   `∃ ε > 0`. DLT's Lemma 3.1 outputs this specific value; weaker
   forms don't thread through the induction. See
   [`design-notes.md §9`](design-notes.md).

2. **`intervalCenter` vs `witnessCenter` split.** DLT's single
   `t_i` plays two roles (cover interval center, witness center).
   Forcing both to be the same point makes the cover-construction
   existence proof intractable under the standard Lebesgue-number
   approach. The formalization separates them (with
   `I_subset_neighborhood` linking). See
   [`design-notes.md §10`](design-notes.md).

3. **`σ` non-monotone in general.** Paper's induction picks the
   "smallest index" at each step; geometric intuition suggests
   `σ` is monotone. Formalization reveals it's not: `σ(l+1)` can
   be less than `σ(l)` if earlier indices were skipped. See
   [`design-notes.md §11`](design-notes.md).

4. **Only even-gap disjointness is provable; TwoFold needs parity
   rescue.** Spacing condition (a) constrains index pairs
   `(i, i+2)` only; chain gives even-gap disjointness but not
   odd-gap. DLT's Lemma 3.2 (TwoFold) follows because for any 3
   distinct σ-indices `a < b < c`, one of `{(a,b), (b,c), (a,c)}`
   has even gap ≥ 2 by parity. The paper's one-sentence claim
   unpacks into this 3-layer structure in Lean. See
   [`design-notes.md §11`](design-notes.md).

5. **`PairableCover` scaffolding was dead weight.** Carried in
   type signatures through v0.1.1 but never load-bearing in the
   proof. Removed in v0.2; see
   [`design-notes.md §§12, 14`](design-notes.md).

## How to build and verify

```bash
lake exe cache get   # first run only, downloads Mathlib oleans
lake build           # zero sorries, zero warnings
lake build test      # smoke test + axiom audit (printed)
lake build examples  # worked example
```

## What's next

Post-v0.2 candidates:

* Multi-parameter cover construction for `K = unitInterval^m`,
  feeding the same `exists_sup_reduction_of_cover`.
* Client instantiation against a concrete GMT setup (out of scope
  for this repo).
