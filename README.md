# CombArg — Almgren–Pitts Combinatorial Argument, Formalized in Lean 4

A Lean 4 formalization of the **combinatorial core** of the
Almgren–Pitts min-max argument: the cover-refinement step
underlying the existence of minimal hypersurfaces, extracted as a
self-contained metric-combinatorial theorem with no
geometric-measure-theoretic dependencies.

## What this library provides

Two public theorems.

### Combinatorial main theorem — `CombArg.Refinement.exists_refinement`

From a continuous `f : unitInterval → ℝ` with `m₀ = sSup (range f)`,
`N > 0`, and a `LocalWitness` at every `1/N`-near-critical
parameter (saving `1/(4N)` each), construct a
`FiniteCoverWithWitnesses unitInterval f m₀ (1/N) (1/(4N))`: a
finite family of closed pieces of `unitInterval` carrying
per-piece replacement energies `E_l` and uniform savings
`s_l = 1/(4N)`, satisfying

  - **(I)** `f − E_l ≥ s_l` on each piece,
  - **(II)** every `t` lies in at most two pieces (two-fold overlap),
  - **(III)** `{t : f t ≥ m₀ − 1/N} ⊆ ⋃ pieces`.

This is the non-trivial content extracted from the DLT-style
1D cover refinement (Lebesgue-number cover, bounded
smallest-index refinement induction, skip-2 parity rescue).

### Sup-reduction bookkeeping corollary — `CombArg.exists_sup_reduction_of_cover`

From any `FiniteCoverWithWitnesses K f m₀ δ ε` on a compact
nonempty space `K` with `ε ≤ δ`, produce a competitor
`f' : K → ℝ` with `f' ≤ f` pointwise, `f' = f` outside the cover
support, and `sSup (range f') ≤ m₀ − ε`. Three-line scalar
arithmetic over the cover data; generic in `K`.

A one-parameter specialization `CombArg.exists_sup_reduction`
chains the two: on `K = unitInterval` with `(δ, ε) = (1/N,
1/(4N))`, given just the witness hypothesis it produces the
sup-reducing competitor directly.

This formalization corresponds to the combinatorial core
appearing in De Lellis–Tasnady (2013) §3.2 and analogous
developments in Pitts (1981), Colding–De Lellis (2003),
De Lellis–Ramic (2017), and Marques–Neves (2014).

## Status

- **Version**: 0.1.1 (April 2026); v0.2 in progress.
- **License**: Apache 2.0.
- **Build**: `lake build` succeeds with no warnings; zero `sorry`.
- **Verification**: depends only on the three standard Lean 4 /
  Mathlib foundational axioms (`propext`, `Classical.choice`,
  `Quot.sound`). Smoke test (`test/Smoke.lean`) prints the audit
  on every CI run.

## Quick start

```bash
git clone https://github.com/MathNetwork/comb_arg.git
cd comb_arg
lake exe cache get   # download Mathlib pre-compiled oleans (first run)
lake build           # main library
lake build test      # smoke test + axiom audit
lake build examples  # worked example
```

See [`examples/MinimalUsage.lean`](examples/MinimalUsage.lean) for
a self-contained worked invocation on `f ≡ 1` parameterized by `N`.

## Public theorems

```lean
-- Combinatorial main theorem.
lemma exists_refinement
    {f : unitInterval → ℝ} (hf : Continuous f)
    (hm : m₀ = sSup (Set.range f))
    (hN : 0 < N)
    (witness : ∀ t : unitInterval, f t ≥ m₀ - 1 / (N : ℝ) →
                 LocalWitness unitInterval f t (1 / (4 * (N : ℝ)))) :
    Nonempty (FiniteCoverWithWitnesses unitInterval f m₀
              (1 / (N : ℝ)) (1 / (4 * (N : ℝ))))

-- Bookkeeping corollary, generic K.
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

-- One-parameter chained corollary on K = unitInterval.
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

See [`docs/project-overview.md`](docs/project-overview.md) for a
narrative tour of the definitions and proof structure.

## Minimal example

```lean
import CombArg

open scoped Classical

-- A LocalWitness for f ≡ 1 with global replacement 1 − 1/(4·N).
noncomputable def constOneWitness (N : ℕ) (t : unitInterval) :
    CombArg.LocalWitness unitInterval (fun _ => (1 : ℝ)) t
                          (1 / (4 * (N : ℝ))) where
  neighborhood := Set.univ
  isOpen_neighborhood := isOpen_univ
  t_mem := Set.mem_univ _
  replacementEnergy := fun _ => 1 - 1 / (4 * (N : ℝ))
  replacementEnergy_continuous := continuous_const
  saving_bound := fun _ _ => by
    show (1 : ℝ) - (1 - 1 / (4 * (N : ℝ))) ≥ 1 / (4 * (N : ℝ))
    linarith

example (N : ℕ) (hN : 0 < N) :
    ∃ (f' : unitInterval → ℝ) (S : Set unitInterval), _ :=
  CombArg.exists_sup_reduction (f := fun _ => (1 : ℝ))
    continuous_const
    (by rw [Set.range_const]; exact (csSup_singleton _).symm) hN
    (fun t _ => constOneWitness N t)
```

The runnable form lives in
[`examples/MinimalUsage.lean`](examples/MinimalUsage.lean).

## Scope

**Provided**:

- `CombArg.Refinement.exists_refinement` — combinatorial main
  theorem on `unitInterval`.
- `CombArg.exists_sup_reduction_of_cover` — bookkeeping corollary,
  generic `K`.
- `CombArg.exists_sup_reduction` — one-parameter chained corollary.
- Input structures `FiniteCoverWithWitnesses` and `LocalWitness`.
- Intermediate 1D structures `InitialCover`, `PartialRefinement`,
  `SkippedSpacedIntervals` and their geometry (skip-2 spacing,
  even-gap disjointness, parity rescue).

**Not provided**:

- Construction of `LocalWitness` instances on
  geometric-measure-theoretic data (this is the caller's
  responsibility; in GMT contexts these come from replacement
  families).
- Geometric-measure-theoretic machinery (varifolds, integral
  currents, Caccioppoli sets, etc.).
- The full min-max existence theorem (only its combinatorial core).
- Multi-parameter applications `K = unitInterval^m`. The
  bookkeeping corollary is already generic in `K`; only an
  additional cover construction is needed.

## Public API stability

The following names are considered stable public API and will not
change without a major version bump:

- `CombArg.Refinement.exists_refinement`
- `CombArg.exists_sup_reduction_of_cover`
- `CombArg.exists_sup_reduction`
- `CombArg.FiniteCoverWithWitnesses` (structure + fields)
- `CombArg.LocalWitness` (structure + fields)
- `CombArg.Refinement.InitialCover` (structure + fields)
- `CombArg.Refinement.PartialRefinement` (structure + fields)
- `CombArg.Refinement.SkippedSpacedIntervals` (structure + fields)
- `CombArg.Refinement.nearCritical`
- `CombArg.Refinement.openInterval`

Internal definitions (`step_succ_at`, `ExtendResult`,
`terminal_twoFold`, chain-spacing lemmas, etc.) may change in
minor releases.

## Repository structure

```
comb_arg/
├── README.md
├── LICENSE                    Apache 2.0
├── CITATION.cff
├── CHANGELOG.md
├── lakefile.lean, lake-manifest.json, lean-toolchain
├── CombArg.lean               top-level facade (re-exports)
├── CombArg/
│   ├── Util.lean              ge_of_closure_of_ge,
│   │                          exists_even_gap_of_three
│   ├── Witness.lean           LocalWitness
│   ├── Core.lean              FiniteCoverWithWitnesses +
│   │                          exists_sup_reduction_of_cover
│   ├── SupReduction.lean      exists_sup_reduction
│   ├── Refinement.lean        facade re-exporting submodules
│   └── Refinement/
│       ├── SpacedIntervals.lean     openInterval +
│       │                            SkippedSpacedIntervals
│       ├── InitialCover.lean        nearCritical + InitialCover
│       ├── CoverConstruction.lean   exists_initialCover
│       ├── PartialRefinement.lean   mid-induction state
│       ├── Induction.lean           step_succ_at +
│       │                            exists_terminal_refinement
│       ├── Disjointness.lean        wrappers over SpacedIntervals
│       └── Assembly.lean            exists_refinement
├── docs/
│   ├── project-overview.md    narrative tour
│   └── design-notes.md        design decisions (§§1–14)
├── examples/
│   └── MinimalUsage.lean      worked invocation
└── test/
    └── Smoke.lean             smoke + axiom audit
```

## Dependencies

- Lean 4 (`leanprover/lean4:v4.30.0-rc2`, pinned in
  `lean-toolchain`).
- Mathlib (pinned via `lake-manifest.json`).
- No other dependencies.

## Citation

See [`CITATION.cff`](CITATION.cff). If you use this library in
academic work, please cite using the metadata there.

## Changelog

See [`CHANGELOG.md`](CHANGELOG.md).

## License

Apache 2.0 — see [`LICENSE`](LICENSE).
