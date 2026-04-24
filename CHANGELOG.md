# Changelog

All notable changes to CombArg will be documented here.
Format based on [Keep a Changelog](https://keepachangelog.com/).

## [0.1.1] — 2026-04-24

### Reframe: combinatorial core vs. bookkeeping corollary, with
### anchoring conjuncts on sup-reduction corollaries

Framing + narrative release, plus a **breaking API change** to the
two sup-reduction corollaries' conclusions (strict superset of the
old guarantee — clients that destructure the old 1-tuple
existential must update to the new 4-tuple / 5-tuple). The axiom
audit (`propext`, `Classical.choice`, `Quot.sound`) is unchanged;
all proof bodies are unchanged; public identifiers keep their
names.

#### Changed

- **Main theorem** is now
  `CombArg.Refinement.exists_refinement` (combinatorial core):
  from a `LocalWitness` family on the near-critical set of
  `f : unitInterval → ℝ`, produce a
  `FiniteCoverWithWitnesses unitInterval f m₀ (1/N) (1/(4N))`
  with two-fold overlap. The non-trivial content
  (Lebesgue-number cover, bounded smallest-index refinement,
  skip-2 parity rescue) lives here.
- `CombArg.exists_sup_reduction_of_cover` is reframed as a
  **sup-reduction bookkeeping corollary** (generic `K`): a
  three-line scalar arithmetic consequence of the combinatorial
  core (or of any independently produced
  `FiniteCoverWithWitnesses`).
- `CombArg.exists_sup_reduction` is reframed as the
  **one-parameter sup-reduction corollary**, composing the
  combinatorial main theorem with the bookkeeping corollary on
  `K = unitInterval` with `(δ, ε) = (1/N, 1/(4N))`.
- `CombArg.lean` top-level facade: imports reordered
  (`Refinement` first) and expanded module docstring reflecting
  the new framing.
- Module and declaration docstrings updated in
  `CombArg/Core.lean`, `CombArg/SupReduction.lean`, and
  `CombArg/Refinement/Assembly.lean`.
- `paper/paper.tex`: §1/§2/§3 and Figure~1 rewritten around the
  new framing. Old `lem:assembly` (§3) merged into the proof of
  the new `thm:core`.
- Paper Theorem 1.3 and Theorem 2.X (§2.2) statement: remove
  non-load-bearing hypotheses (ambient pseudo-metric $X$ with
  `PairableCover X`, and the dead $m_0 > 0$ hypothesis). A new
  Remark~\ref{rem:lean-scaffolding} records the Lean-side
  scaffolding.
- `docs/design-notes.md` §13 records the reframe rationale.

#### Changed (breaking: conclusion strengthened)

- `exists_sup_reduction_of_cover` conclusion **strengthened** from
  `∃ f', sSup (range f') ≤ m₀ − ε` to
  `∃ f', (∀ t, f' t ≤ f t) ∧ (∀ t ∉ ⋃ l, C.piece l, f' t = f t)
  ∧ sSup (range f') ≤ m₀ − ε`. The two new conjuncts anchor the
  competitor to `f` (pointwise dominance and localization off the
  cover's support), ruling out trivial constant witnesses and
  making the statement genuinely quantitative. Proof is unchanged
  at the mathematical level; two short lemmas extracted:
  `reducedEnergy_le_f`,
  `reducedEnergy_eq_of_not_mem_iUnion_piece`.
- `exists_sup_reduction` conclusion **strengthened** similarly,
  additionally exposing the modification set `S ⊆ unitInterval`
  (the union of cover pieces) and its coverage of the
  `1/N`-near-critical set. New signature:
  `∃ (f' : unitInterval → ℝ) (S : Set unitInterval), {t | f t ≥
  m₀ − 1/N} ⊆ S ∧ (∀ t, f' t ≤ f t) ∧ (∀ t ∉ S, f' t = f t) ∧
  sSup (range f') ≤ m₀ − 1/(4N)`.
- `examples/MinimalUsage.lean`: docstring-level `example`
  updated to the new conclusion shape.
- `README.md` public-theorem code blocks updated to the new
  signatures.

#### Unchanged

- All proof bodies (Core.lean's existence witness is still
  `C.reducedEnergy`, SupReduction.lean still chains
  `exists_refinement` through the bookkeeping corollary).
- `exists_refinement` signature (only strengthening is on the
  two sup-reduction corollaries downstream).
- `FiniteCoverWithWitnesses`, `LocalWitness`, `PairableCover`,
  and all supporting structures.
- `#print axioms` for all public theorems: still
  `[propext, Classical.choice, Quot.sound]`.
- `lake build` / `lake build test` / `lake build examples`:
  still all green.

#### Known follow-ups

- `README.md` and `docs/project-overview.md` still describe
  `exists_sup_reduction_of_cover` as "abstract core"; align
  with the paper framing in the next substantive documentation
  pass (tracked alongside the PairableCover §12 resolution).

[0.1.1]: https://github.com/MathNetwork/comb_arg/releases/tag/v0.1.1

## [0.1.0] — 2026-04-23

### Initial release

First public release of the Almgren–Pitts combinatorial argument
formalization.

#### Added

- **Abstract core theorem** `CombArg.exists_sup_reduction_of_cover`
  (`CombArg/Core.lean`): given a continuous `f : K → ℝ` on a
  compact nonempty space `K` with `m₀ = sSup (range f)` and scalars
  `0 < ε ≤ δ`, from a `FiniteCoverWithWitnesses K f m₀ δ ε` produce
  a competitor `f'` with `sSup (range f') ≤ m₀ − ε`. Parameterizes
  the near-critical threshold `δ` and the per-piece saving floor `ε`.
- **One-parameter application** `CombArg.exists_sup_reduction`
  (`CombArg/SupReduction.lean`): specializes the core to
  `K = unitInterval`, `δ = 1/N`, `ε = 1/(4N)`. Given a continuous
  `f : unitInterval → ℝ` with `m₀ = sSup (range f) > 0`, `N > 0`,
  and a `LocalWitness` with saving `1/(4N)` at every
  `1/N`-near-critical parameter, produce `f'` with
  `sSup (range f') ≤ m₀ − 1/(4N)`.
- Cover structure `FiniteCoverWithWitnesses` (`CombArg/Core.lean`):
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
- Abstract 1D geometry: `Refinement.SkippedSpacedIntervals`
  (`CombArg/Refinement/SpacedIntervals.lean`) — a finite family of
  open intervals on `unitInterval` specified by centers and positive
  radii under the skip-2 spacing condition, carrying the purely
  geometric content of DLT's spacing (a): `chain_spacing`,
  `disjoint_of_even_gap`, `closure_disjoint_of_even_gap`,
  `not_three_overlap`, `not_three_overlap_any_order`.
  `InitialCover` projects to this via
  `InitialCover.toSkippedSpacedIntervals`.
- Disjointness structure: `InitialCover.chain_spacing`,
  `InitialCover.disjoint_of_even_gap`,
  `InitialCover.closure_disjoint_of_even_gap`,
  `InitialCover.not_three_overlap` — thin wrappers over the
  `SkippedSpacedIntervals` lemmas; the three-layer parity
  argument is documented in `docs/design-notes.md §11`.
- Reusable utilities (`CombArg/Util.lean`):
  `ge_of_closure_of_ge` — extend a closed-half-line condition from
  a set to its closure via continuity;
  `exists_even_gap_of_three` — purely arithmetic three-indices →
  even-gap pair lemma, discharged by `omega`.
- 1D assembly: `terminal_twoFold`, `saving_bound_closure`,
  `exists_refinement` (output now a `FiniteCoverWithWitnesses`).

#### Verified

- Zero `sorry` across the entire library.
- `#print axioms CombArg.exists_sup_reduction` depends only
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
