# Changelog

All notable changes to CombLemma will be documented here.
Format based on [Keep a Changelog](https://keepachangelog.com/).

## [0.1.0] — 2026-04-23

### Initial release

First public release of the Almgren–Pitts combinatorial lemma
formalization.

#### Added

- Main theorem `CombLemma.exists_sup_reduction`: given a
  continuous `f : unitInterval → ℝ` with `m₀ = sSup (range f) > 0`,
  a near-criticality parameter `N > 0`, and a `LocalWitness` with
  saving `1/(4N)` at every `1/N`-near-critical parameter, produce a
  competitor `f'` with `sSup (range f') ≤ m₀ − 1/(4N)`.
- Input interface: `LocalWitness` structure bundling an open
  neighborhood, a paired cover, a continuous replacement energy, and
  the quantitative saving bound.
- Abstract cover class: `PairableCover` with `Cover`, `leftRegion`,
  `rightRegion`, `diameter`, `regions_disjoint`, and
  `diameter_nesting`.
- Supporting structures: `EnergyBound.Refinement`,
  `Refinement.InitialCover`, `Refinement.PartialRefinement`.
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
- Assembly: `terminal_twoFold`, `saving_bound_closure`,
  `exists_refinement`.
- Arithmetic bookkeeping (`CombLemma/EnergyBound.lean`) tying the
  quantitative `1/(4N)` bound.

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
  signatures but not referenced by the proof of
  `exists_sup_reduction`. See
  [`docs/design-notes.md §12`](docs/design-notes.md) for the pending
  A/B/C decision (retain as extension point / rework to load-bearing /
  simplify out). Resolution planned for v0.2.
- Single-parameter sweepouts only: the main theorem specializes to
  `K = unitInterval`. Abstract-`K` generalization is planned work
  (see [`docs/design-notes.md §4`](docs/design-notes.md)).
- No stock `PairableCover` instances shipped beyond the trivial one
  on `ℝ` in `test/Smoke.lean`.

[0.1.0]: https://github.com/MathNetwork/comb_arg/releases/tag/v0.1.0
