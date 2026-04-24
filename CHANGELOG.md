# Changelog

All notable changes to CombLemma will be documented here.
Format based on [Keep a Changelog](https://keepachangelog.com/).

## [0.1.0] — 2026-04-23

### Initial release

First public release of the Almgren–Pitts combinatorial lemma
formalization.

#### Added

- **Abstract core theorem** `CombLemma.exists_sup_reduction_of_cover`
  (`CombLemma/Core.lean`): given a continuous `f : K → ℝ` on a
  compact nonempty space `K` with `m₀ = sSup (range f)` and scalars
  `0 < ε ≤ δ`, from a `FiniteCoverWithWitnesses K f m₀ δ ε` produce
  a competitor `f'` with `sSup (range f') ≤ m₀ − ε`. Parameterizes
  the near-critical threshold `δ` and the per-piece saving floor `ε`.
- **One-parameter application** `CombLemma.exists_sup_reduction`
  (`CombLemma/SupReduction.lean`): specializes the core to
  `K = unitInterval`, `δ = 1/N`, `ε = 1/(4N)`. Given a continuous
  `f : unitInterval → ℝ` with `m₀ = sSup (range f) > 0`, `N > 0`,
  and a `LocalWitness` with saving `1/(4N)` at every
  `1/N`-near-critical parameter, produce `f'` with
  `sSup (range f') ≤ m₀ − 1/(4N)`.
- Cover structure `FiniteCoverWithWitnesses` (`CombLemma/Core.lean`):
  finite multiplicity-bounded cover of the `δ`-near-critical set,
  per-piece savings `≥ ε`, with replacement energies and the
  `twoFold` invariant. The abstract input to the core theorem.
- Input interface: `LocalWitness` structure bundling an open
  neighborhood, a paired cover, a continuous replacement energy, and
  the quantitative saving bound.
- Abstract cover class: `PairableCover` with `Cover`, `leftRegion`,
  `rightRegion`, `diameter`, `regions_disjoint`, and
  `diameter_nesting`.
- Supporting structures: `Refinement.InitialCover`,
  `Refinement.PartialRefinement`.
- Near-critical set analysis: `nearCritical`, `isCompact_nearCritical`,
  `nearCritical_nonempty`.
- Initial cover construction: `exists_initialCover` — a grid plus
  Lebesgue-number argument on the compact sublevel set producing an
  `InitialCover` with explicit `intervalCenter`, `radius`,
  `witnessCenter` fields, satisfying DLT's spacing condition (a).
- Refinement induction: `step_zero`, `step_succ`, `step_succ_at`,
  `exists_terminal_refinement` — bounded iteration via smallest-index
  selection with two-case dispatch, producing a terminal
  `PartialRefinement` with injective `σ`.
- Disjointness structure: `InitialCover.chain_spacing`,
  `InitialCover.disjoint_of_even_gap`,
  `InitialCover.closure_disjoint_of_even_gap`,
  `InitialCover.not_three_overlap` — the three-layer parity
  argument documented in `docs/design-notes.md §11`.
- 1D assembly: `terminal_twoFold`, `saving_bound_closure`,
  `exists_refinement` (output now a `FiniteCoverWithWitnesses`).

#### Verified

- Zero `sorry` across the entire library.
- `#print axioms CombLemma.exists_sup_reduction` depends only
  on `propext`, `Classical.choice`, `Quot.sound` — the three standard
  Lean 4 / Mathlib foundational axioms.
- CI (GitHub Actions) runs `lake build`, `lake build test`, and
  `lake build examples` on every push.

#### Documentation

- [`README.md`](README.md) — library overview, quick start, scope,
  public API boundary.
- [`docs/project-overview.md`](docs/project-overview.md) — guided API
  tour.
- [`docs/design-notes.md`](docs/design-notes.md) — twelve sections
  covering design decisions and formalization findings.
- [`examples/MinimalUsage.lean`](examples/MinimalUsage.lean) —
  downstream invocation pattern (documentation-form).

#### Known limitations

- `PairableCover` is scaffolding: the class is carried in type
  signatures but not referenced by the proof of the core theorem.
  See [`docs/design-notes.md §12`](docs/design-notes.md) for the
  pending A/B/C decision (retain as extension point / rework to
  load-bearing / simplify out). Resolution planned for v0.2.
- Single-parameter applications only: a second application for
  `K = unitInterval^m` (multi-parameter sweepouts) is planned for
  a future release. The abstract core `exists_sup_reduction_of_cover`
  is already generic in `K`; only an additional cover construction
  is required.
- No stock `PairableCover` instances shipped beyond the trivial one
  on `ℝ` in `test/Smoke.lean`.

[0.1.0]: https://github.com/MathNetwork/comb_arg/releases/tag/v0.1.0
