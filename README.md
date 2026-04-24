# CombArg: The Almgren-Pitts Combinatorial Argument, Formalized in Lean 4

A Lean 4 formalization of the **Almgren–Pitts combinatorial argument** — the
quantitative covering-refinement argument underlying min-max constructions
of minimal hypersurfaces.

## What this library provides

A single main theorem, `CombArg.exists_sup_reduction`: given a
continuous function `f : unitInterval → ℝ` on the unit interval, a
supremum `m₀ = sSup (range f)`, a near-criticality parameter `N > 0`, and
at every `1/N`-near-critical parameter a `LocalWitness` with saving
`1/(4N)`, produce a modified function `f' : unitInterval → ℝ` with the
quantitative improvement `sSup (range f') ≤ m₀ − 1/(4N)`.

This is the combinatorial core of the argument appearing in Pitts (1981),
Colding–De Lellis (2003), De Lellis–Tasnady (2013), De Lellis–Ramic
(2017), Marques–Neves's Morse index work, and subsequent min-max
literature, now extracted as a standalone machine-verified theorem with
no geometric-measure-theoretic dependencies.

## Status

- **Version**: 0.1.0 (initial release)
- **License**: Apache 2.0
- **Build**: `lake build` — all 1392 jobs green
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
#print axioms CombArg.exists_sup_reduction' > /tmp/audit.lean
lake env lean /tmp/audit.lean
# Expected: depends on axioms: [propext, Classical.choice, Quot.sound]
```

See [`examples/MinimalUsage.lean`](examples/MinimalUsage.lean) for a
worked invocation pattern.

## Core result

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

See [`docs/project-overview.md`](docs/project-overview.md) for a narrative
tour of the definitions and proof structure.

## Scope

**This library provides**:

- `exists_sup_reduction` — the main theorem
- `LocalWitness` — input interface for per-point reducers
- `PairableCover` — abstract class for paired-cover structures
- `Refinement`, `InitialCover`, `PartialRefinement` — intermediate
  structures
- `exists_refinement` — explicit constructive refinement used
  internally by the main theorem

**This library does NOT provide**:

- Construction of `LocalWitness` instances (the downstream user's
  responsibility; in GMT contexts, via replacement families)
- Any geometric-measure-theoretic machinery (varifolds, integral
  currents, Caccioppoli sets, etc.)
- The full min-max theorem (only its combinatorial component)
- Stock instances of `PairableCover` beyond a trivial smoke-test
  instance on `ℝ`
- Abstract-`K` generalization (the main theorem specializes to
  `K = unitInterval`; see [`docs/design-notes.md §4`](docs/design-notes.md))

## Public API (v0.1 stability)

The following names are considered stable public API and will not change
without a major version bump:

- `CombArg.exists_sup_reduction` — main theorem
- `CombArg.LocalWitness` (structure + fields)
- `CombArg.PairableCover` (class + fields)
- `CombArg.EnergyBound.Refinement` (structure + fields)
- `CombArg.Refinement.InitialCover` (structure + fields)
- `CombArg.Refinement.PartialRefinement` (structure + fields)
- `CombArg.Refinement.nearCritical`
- `CombArg.Refinement.exists_refinement`

Internal definitions (`step_succ`, `step_succ_at`, `terminal_twoFold`,
chain-spacing lemmas, etc.) may change in minor releases. Consumers
relying on internal definitions do so at their own risk.

## Repository structure

```
comb-arg/
├── README.md
├── LICENSE                    Apache 2.0
├── CITATION.cff
├── CHANGELOG.md
├── lakefile.lean, lake-manifest.json, lean-toolchain
├── CombArg.lean             top-level module (re-exports)
├── CombArg/
│   ├── Witness.lean           PairableCover class, LocalWitness structure
│   ├── EnergyBound.lean       arithmetic: Refinement → quantitative bound
│   ├── SupReduction.lean      top-level exists_sup_reduction
│   ├── Refinement.lean        (facade re-exporting the 6 submodules)
│   └── Refinement/
│       ├── InitialCover.lean  nearCritical + InitialCover
│       ├── CoverConstruction.lean   exists_initialCover (Lebesgue)
│       ├── PartialRefinement.lean   mid-induction state + step_zero
│       ├── Induction.lean     step_succ + exists_terminal_refinement
│       ├── Disjointness.lean  spacing + parity-rescue lemmas
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
3. [`CombArg/EnergyBound.lean`](CombArg/EnergyBound.lean)
   — `Refinement` structure + arithmetic bookkeeping.
4. [`CombArg/Refinement.lean`](CombArg/Refinement.lean)
   — refinement-construction facade + six submodules under `Refinement/`.
5. [`CombArg/SupReduction.lean`](CombArg/SupReduction.lean)
   — the top-level chain.
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
