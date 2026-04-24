# CombArg: The Almgren-Pitts Combinatorial Argument, Formalized in Lean 4

A Lean 4 formalization of the **Almgren–Pitts combinatorial argument** — the
quantitative covering-refinement argument underlying min-max constructions
of minimal hypersurfaces.

## What this library provides

Two main theorems.

**Abstract core** — `CombArg.exists_sup_reduction_of_cover`. Given a
compact nonempty topological space `K`, a continuous `f : K → ℝ` with
`m₀ = sSup (range f)`, scalars `0 < ε ≤ δ`, and a
`FiniteCoverWithWitnesses` of the `δ`-super-level set (a finite cover
with per-piece replacement energies, per-piece saving floor `ε`, and
two-fold overlap), produce `f' : K → ℝ` with
`sSup (range f') ≤ m₀ − ε`.

**One-parameter application** — `CombArg.exists_sup_reduction`.
Specializes the core to `K = unitInterval` with `δ = 1/N` and
`ε = 1/(4N)`. Given a continuous `f` and a `LocalWitness` at every
`1/N`-near-critical parameter (saving `1/(4N)` each), produce `f'` with
`sSup (range f') ≤ m₀ − 1/(4N)`. The 1D cover-refinement that feeds the
core is done internally.

This is the combinatorial core of the argument appearing in Pitts (1981),
Colding–De Lellis (2003), De Lellis–Tasnady (2013), De Lellis–Ramic
(2017), and Marques–Neves (2014), extracted as a standalone
machine-verified result with no geometric-measure-theoretic dependencies.

## Status

- **Version**: 0.1.0 (initial release)
- **License**: Apache 2.0
- **Build**: `lake build` — 1536 jobs, all green
- **Verification**: zero `sorry`, depends only on the three standard Lean 4 /
  Mathlib foundational axioms (`propext`, `Classical.choice`, `Quot.sound`)

## Quick start

```bash
git clone <this repo>
cd comb-arg
lake exe cache get   # download Mathlib pre-compiled oleans (first run)
lake build           # main build — zero sorries
lake build test      # smoke test
```

Axiom audit:

```bash
echo 'import CombArg
#print axioms CombArg.exists_sup_reduction_of_cover
#print axioms CombArg.exists_sup_reduction' > /tmp/audit.lean
lake env lean /tmp/audit.lean
# Expected (both): depends on axioms: [propext, Classical.choice, Quot.sound]
```

See [`examples/MinimalUsage.lean`](examples/MinimalUsage.lean) for a
worked invocation pattern.

## Public theorems

```lean
-- Abstract core: generic compact K, parameters (δ, ε) with ε ≤ δ.
theorem exists_sup_reduction_of_cover
    {K : Type*} [TopologicalSpace K] [CompactSpace K] [Nonempty K]
    {f : K → ℝ} (hf : Continuous f)
    {m₀ : ℝ} (hm : m₀ = sSup (Set.range f))
    {δ ε : ℝ} (_hδ : 0 < δ) (_hε : 0 < ε) (hle : ε ≤ δ)
    (C : FiniteCoverWithWitnesses K f m₀ δ ε) :
    ∃ f' : K → ℝ,
      (∀ t, f' t ≤ f t) ∧
      (∀ t, t ∉ (⋃ l, C.piece l) → f' t = f t) ∧
      sSup (Set.range f') ≤ m₀ - ε

-- One-parameter application: K = unitInterval, δ = 1/N, ε = 1/(4N).
theorem exists_sup_reduction
    {X : Type*} [PseudoMetricSpace X] [PairableCover X]
    {f : unitInterval → ℝ} (hf : Continuous f)
    {m₀ : ℝ} (hm_pos : 0 < m₀) (hm : m₀ = sSup (Set.range f))
    {N : ℕ} (hN : 0 < N)
    (witness : ∀ t : unitInterval, f t ≥ m₀ - 1 / (N : ℝ) →
                  Nonempty (LocalWitness unitInterval X f t (1 / (4 * (N : ℝ))))) :
    ∃ (f' : unitInterval → ℝ) (S : Set unitInterval),
      {t : unitInterval | f t ≥ m₀ - 1 / (N : ℝ)} ⊆ S ∧
      (∀ t, f' t ≤ f t) ∧
      (∀ t, t ∉ S → f' t = f t) ∧
      sSup (Set.range f') ≤ m₀ - 1 / (4 * (N : ℝ))
```

See [`docs/project-overview.md`](docs/project-overview.md) for a narrative
tour of the definitions and proof structure.

## Scope

**This library provides**:

- `exists_sup_reduction_of_cover` — abstract core (generic `K`)
- `exists_sup_reduction` — one-parameter application on `unitInterval`
- `FiniteCoverWithWitnesses` — input structure to the core
- `LocalWitness` — per-point reducer data for the application
- `PairableCover` — abstract class for paired-cover structures
- `InitialCover`, `PartialRefinement` — intermediate 1D structures
- `exists_refinement` — the 1D cover-refinement feeding the core

**This library does NOT provide**:

- Construction of `LocalWitness` instances (caller's responsibility;
  in GMT contexts these come from replacement families)
- Geometric-measure-theoretic machinery (varifolds, integral currents,
  Caccioppoli sets, etc.)
- The full min-max existence theorem (only its combinatorial core)
- Stock instances of `PairableCover` beyond a trivial smoke-test
  instance on `ℝ`
- Multi-parameter application `K = unitInterval^m` (the core accepts
  any compact `K`, but only the 1D cover construction is shipped)

## Public API (v0.1 stability)

The following names are considered stable public API and will not change
without a major version bump:

- `CombArg.exists_sup_reduction_of_cover` — abstract core theorem
- `CombArg.exists_sup_reduction` — one-parameter application
- `CombArg.FiniteCoverWithWitnesses` (structure + fields)
- `CombArg.LocalWitness` (structure + fields)
- `CombArg.PairableCover` (class + fields)
- `CombArg.Refinement.InitialCover` (structure + fields)
- `CombArg.Refinement.PartialRefinement` (structure + fields)
- `CombArg.Refinement.nearCritical`
- `CombArg.Refinement.exists_refinement`

Internal definitions (`step_succ`, `step_succ_at`, `terminal_twoFold`,
chain-spacing lemmas, etc.) may change in minor releases.

## Repository structure

```
comb-arg/
├── README.md
├── LICENSE                    Apache 2.0
├── CITATION.cff
├── CHANGELOG.md
├── lakefile.lean, lake-manifest.json, lean-toolchain
├── CombArg.lean               top-level module (re-exports)
├── CombArg/
│   ├── Util.lean              reusable utilities
│   │                          (ge_of_closure_of_ge, exists_even_gap_of_three)
│   ├── Witness.lean           PairableCover class, LocalWitness structure
│   ├── Core.lean              FiniteCoverWithWitnesses +
│   │                          exists_sup_reduction_of_cover (abstract core)
│   ├── EnergyBound.lean       re-export stub (subsumed by Core as of v0.2)
│   ├── SupReduction.lean      exists_sup_reduction (one-parameter application)
│   ├── Refinement.lean        facade re-exporting the 7 submodules
│   └── Refinement/
│       ├── SpacedIntervals.lean     abstract skip-2 spaced intervals
│       │                            (SkippedSpacedIntervals + geometry lemmas)
│       ├── InitialCover.lean  nearCritical + InitialCover
│       ├── CoverConstruction.lean   exists_initialCover (Lebesgue)
│       ├── PartialRefinement.lean   mid-induction state + step_zero
│       ├── Induction.lean     step_succ + exists_terminal_refinement
│       ├── Disjointness.lean  spacing + parity-rescue lemmas
│       │                      (thin wrappers over SpacedIntervals)
│       └── Assembly.lean      terminal_twoFold, saving_bound_closure,
│                              exists_refinement
├── docs/
│   ├── project-overview.md    narrative status + reading guide
│   └── design-notes.md        design decisions (§§1–12)
├── examples/
│   └── MinimalUsage.lean      worked invocation pattern
└── test/
    └── Smoke.lean             PairableCover smoke test
```

## For contributors

Reading order:

1. [`docs/project-overview.md`](docs/project-overview.md) — current
   status and definition tour.
2. [`CombArg/Witness.lean`](CombArg/Witness.lean)
   — `PairableCover`, `LocalWitness`.
3. [`CombArg/Core.lean`](CombArg/Core.lean)
   — `FiniteCoverWithWitnesses` structure + the abstract core theorem
   and its arithmetic bookkeeping.
4. [`CombArg/Refinement.lean`](CombArg/Refinement.lean)
   — 1D cover-construction facade + six submodules under `Refinement/`.
5. [`CombArg/SupReduction.lean`](CombArg/SupReduction.lean)
   — the top-level chain for the one-parameter application.
6. [`docs/design-notes.md`](docs/design-notes.md) — rationale for each
   structural choice.

## Dependencies

- Lean 4 (`leanprover/lean4:v4.30.0-rc2`, pinned in `lean-toolchain`)
- Mathlib (pinned via `lake-manifest.json`)
- No other dependencies

## Citation

See [`CITATION.cff`](CITATION.cff). If you use this library in academic
work, please cite using the metadata there.

## Changelog

See [`CHANGELOG.md`](CHANGELOG.md).

## License

Apache 2.0 — see [`LICENSE`](LICENSE).
