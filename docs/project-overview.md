# Project overview

**Date:** 2026-04-24
**Status:** Zero sorries across all four core modules. Phase 1 and
Phase 2 complete. No dependency on custom axioms; only the three
standard Lean 4 / Mathlib foundational axioms
(`propext`, `Classical.choice`, `Quot.sound`) transitively used.

## Goal

Machine-verified, sorry-free formalization of the combinatorial core
of De Lellis–Tasnady (2013) §3.2 ("Step 1" interval refinement +
"Step 2" arithmetic bookkeeping), factored as a self-contained
metric-combinatorial theorem independent of any
geometric-measure-theory content.

## Top-level theorem

[`CombArg/SupReduction.lean`](../CombArg/SupReduction.lean):

```lean
theorem exists_sup_reduction
    {X : Type*} [PseudoMetricSpace X] [PairableCover X]
    {f : unitInterval → ℝ} (hf : Continuous f)
    {m₀ : ℝ} (hm_pos : 0 < m₀) (hm : m₀ = sSup (Set.range f))
    {N : ℕ} (hN : 0 < N)
    (witness : ∀ t : unitInterval, f t ≥ m₀ - 1 / (N : ℝ) →
                  Nonempty (LocalWitness unitInterval X f t (1 / (4 * (N : ℝ))))) :
    ∃ f' : unitInterval → ℝ, sSup (Set.range f') ≤ m₀ - 1 / (4 * (N : ℝ))
```

**Reading the hypotheses (DLT §3.2 correspondence):**

* `f : unitInterval → ℝ` — the scalar energy (paper's `E` on a
  one-parameter sweepout). Specialized to `unitInterval` per
  [`design-notes.md §4`](design-notes.md); abstract-`K` generalization
  is Phase 3.
* `hm : m₀ = sSup (range f)` — `m₀` is the sup of `f`. The
  corresponding min-max interpretation (as infimum over admissible
  classes) is an external framing the client supplies.
* `N : ℕ` with `hN : 0 < N` — the near-criticality parameter; the
  theorem's output is `1/(4N)` quantitative.
* `witness` — paper's Lemma 3.1 output (existence of a replacement
  family): at every near-critical parameter, a `LocalWitness` with
  saving **exactly** `1/(4N)`. See
  [`design-notes.md §9`](design-notes.md) for the commitment to
  `1/(4N)` over the weaker `∃ ε > 0` form.

**Reading the conclusion:** `f'` undercuts `m₀` by at least `1/(4N)`
uniformly. This is the "reduced energy" of the paper's Step 2.

## Proof architecture

The proof is a two-stage decomposition:

### Phase 1 — Energy bound (`EnergyBound.lean`)

Given a `Refinement K X f m₀ N` (a finite collection of pieces with
local replacement energies satisfying `twoFold` overlap control and
`saving_ge_quarter_N` saving floor), produce a scalar function `f'`
with `sSup (range f') ≤ m₀ − 1/(4N)`.

Key consumed invariants:

* `twoFold` — every `t` lies in at most 2 pieces (bounds multiplicity
  in `reducedEnergy`'s sum-of-savings subtraction).
* `saving_ge_quarter_N` — each piece's saving is at least `1/(4N)`
  (gives the pointwise floor).
* `covers_near_critical` — pieces cover the near-critical set
  (complement uses `f t < m₀ − 1/N ≤ m₀ − 1/(4N)`).

### Phase 2 — Refinement (`Refinement.lean`)

Given the witness hypothesis, produce a `Refinement` by the DLT-style
interval refinement induction. Sub-steps:

* **Phase 2.0** (`exists_initialCover`): from the witness hypothesis
  plus `nearCritical` compactness, build an `InitialCover` — a family
  of intervals `I_i = (intervalCenter i − radius i, intervalCenter i +
  radius i)` satisfying DLT's spacing condition (a)
  (`intervalCenter i + radius i < intervalCenter (i+2) − radius
  (i+2)`) and covering the near-critical set. Construction: grid
  `c_k := k/M` for `M > 4/λ` (λ from Lebesgue number) plus a filter
  keeping grid points near NC; witness centers picked via Lebesgue.
* **Phase 2.1** (`exists_terminal_refinement`): iterate the DLT
  induction `step_zero` → `step_succ_at` × `ic.n` times, producing a
  `PartialRefinement ic L` with `Function.Injective pr.σ` and
  `∀ i, ic.I i ⊆ ⋃ pr.J k`.
* **Phase 2.2** (assembly in `exists_refinement`): package as
  `EnergyBound.Refinement` with `piece k := closure (pr.J k)`,
  `saving k := 1/(4N)` uniform. `twoFold` via
  `terminal_twoFold` (parity argument on even-gap chain disjointness);
  `saving_bound` via `saving_bound_closure` (sequence-limit
  extension using `LocalWitness.replacementEnergy_continuous`).

## Definition tour

### `Witness.lean`

* `PairableCover X` — typeclass on a pseudo-metric space with
  abstract `Cover` type, `leftRegion` / `rightRegion`
  projections, `diameter` scalar, and a `diameter_nesting` axiom.
  Not load-bearing in the current proof (see [note on finding
  below](#finding-diameter_nesting-unused)).
* `LocalWitness K X f t ε` — structure bundling an open neighborhood,
  a cover, a replacement-energy function (with `Continuous`
  requirement), and a quantitative `saving_bound` on the
  neighborhood.

### `EnergyBound.lean`

* `Refinement K X f m₀ N` — finite collection of pieces covering the
  near-critical set, with `twoFold`, `saving_ge_quarter_N`,
  `saving_bound` invariants.
* `Refinement.reducedEnergy` — the scalar `f'` via `f − Σ saving`
  over `piecesContaining`.
* `exists_reducedEnergy_sup_lt` — the arithmetic target.

### `Refinement.lean` (facade) and submodules under `Refinement/`

* `Refinement/InitialCover.lean` — `nearCritical` and its closedness /
  compactness / nonemptiness; `InitialCover` structure (specialized to
  `K = unitInterval`) with `intervalCenter`, `radius`, `witnessCenter`
  (split per [`design-notes.md §10`](design-notes.md)),
  `two_fold_spacing`, `I_subset_neighborhood`, `covers`;
  `exists_closedBall_subset_of_open` (auxiliary).
* `Refinement/CoverConstruction.lean` — `exists_initialCover` via a
  grid + Lebesgue-number construction.
* `Refinement/PartialRefinement.lean` — `PartialRefinement ic l`
  mid-induction state with `J`, `σ`, `J_subset`, `processed_cover`;
  base case `step_zero`.
* `Refinement/Induction.lean` — `step_succ` (paper-faithful
  smallest-index via `Finset.min'`), `step_succ_at` (explicit `i_star`,
  returns `Subtype` with covered-property bundled),
  `exists_terminal_refinement` (strong induction on `remaining.card`).
* `Refinement/Disjointness.lean` —
  `InitialCover.chain_spacing`,
  `InitialCover.disjoint_of_even_gap`,
  `InitialCover.closure_disjoint_of_even_gap`,
  `InitialCover.not_three_overlap`
  (parity-rescue argument; see [`design-notes.md §11`](design-notes.md)).
* `Refinement/Assembly.lean` — `terminal_twoFold` (TwoFold via parity
  rescue + σ-injectivity), `saving_bound_closure` (saving-bound
  extension from `J k` to `closure (J k)` via continuity),
  `exists_refinement` (assembly into `EnergyBound.Refinement`).

### `SupReduction.lean`

* `exists_sup_reduction` — the top-level theorem; chains
  `exists_refinement` and `exists_reducedEnergy_sup_lt`.

## Axiom dependencies

Verified via `#print axioms`:

```
exists_sup_reduction : [propext, Classical.choice, Quot.sound]
```

Only the three standard Lean 4 / Mathlib foundational axioms. The
combinatorial core is independent of any geometric-measure-theory
content; no custom axioms are declared in the library.

## Findings surfaced by formalization

These are paper-level findings the formalization process surfaced
that the DLT argument compresses. Short form:

1. **Witness threshold is quantitative, not existential.** The
   hypothesis `Nonempty (LocalWitness … ε)` must commit to
   `ε = 1/(4N)` exactly, not `∃ ε > 0`. DLT's Lemma 3.1 outputs this
   specific value; weaker forms don't thread through the induction.
   See [`design-notes.md §9`](design-notes.md).
2. **`intervalCenter` vs `witnessCenter` split.** DLT's single `t_i`
   plays two roles (cover interval center, witness center). Forcing
   both to be the same point makes Phase 2.0's existence proof
   intractable under the standard Lebesgue-number approach. The
   formalization separates them (with `I_subset_neighborhood` linking). See
   [`design-notes.md §10`](design-notes.md).
3. **`σ` non-monotone in general.** Paper's induction picks the
   "smallest index" at each step; the geometric intuition suggests
   `σ` is monotone. Formalization reveals it's not: `σ(l+1)` can be
   less than `σ(l)` if earlier indices were skipped. See
   [`design-notes.md §11`](design-notes.md).
4. **Only even-gap disjointness is provable; TwoFold needs parity
   rescue.** Spacing condition (a) constrains index pairs `(i, i+2)`
   only; chain gives even-gap disjointness but not odd-gap. DLT's
   Lemma 3.2 (TwoFold) follows because for any 3 distinct σ-indices
   `a < b < c`, one of `{(a,b), (b,c), (a,c)}` has even gap ≥ 2 by
   parity. The paper's one-sentence claim unpacks into this 3-layer
   structure in Lean. See [`design-notes.md §11`](design-notes.md).

<a name="finding-diameter_nesting-unused"></a>

5. **`diameter_nesting` axiom unused.** The `PairableCover.diameter`
   field and the `diameter_nesting` axiom were anticipated for the
   Phase 2 induction. The actual proof uses `two_fold_spacing` on
   explicit radii and never invokes `diameter_nesting`. The axiom is
   preserved for compatibility with future variants but does not
   appear in the current proof chain.

## How to build and verify

```bash
lake exe cache get   # first run only, downloads Mathlib oleans
lake build           # zero sorries, zero warnings
lake build test      # smoke test

# Axiom audit:
echo 'import CombArg
#print axioms CombArg.exists_sup_reduction' > /tmp/audit.lean
lake env lean /tmp/audit.lean
# Expected: depends on axioms: [propext, Classical.choice, Quot.sound]
```

## What's next

Post-v0.1 candidates:

* Abstract-`K` generalization (remove `unitInterval` specialization).
* Client instantiation against a concrete GMT setup (out of scope for
  this repo).
* `PairableCover` scaffolding vs. load-bearing decision (see
  [`design-notes.md §12`](design-notes.md)).
