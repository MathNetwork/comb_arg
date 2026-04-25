# Changelog

All notable changes to CombArg will be documented here.
Format based on [Keep a Changelog](https://keepachangelog.com/).

## [0.2.0] — 2026-04-25

### API simplification: PairableCover removed, witness shape unwrapped

Reviewer-driven cleanup pass. **Breaking** changes to public
signatures: the `X : Type*` ambient-space parameter, the
`[PseudoMetricSpace X] [PairableCover X]` instance constraints,
the `Nonempty` wrapper around `LocalWitness` in witness
hypotheses, and several unused positivity arguments are all
removed. Axiom audit unchanged.

#### Removed (breaking)

- `class PairableCover X`, `PairableCover.combinedRegion`, and
  `PairableCover.diameter_nesting_combined`. These were
  scaffolding from Phase 0/1 that never became load-bearing in
  the proof; see `docs/design-notes.md` §12 for the option-A/B/C
  analysis and §14 for the v0.2 resolution (option C).
- `LocalWitness.cover` field. The `X` type parameter on
  `LocalWitness` (and on `InitialCover`, `PartialRefinement`,
  `exists_refinement`, `exists_sup_reduction`) goes with it.
- `CombArg/EnergyBound.lean` (re-export stub from the v0.1.1
  reframe, unused).

#### Changed (breaking)

- `LocalWitness K X f t ε` → `LocalWitness K f t ε`.
- `exists_refinement`, `exists_sup_reduction`: witness hypothesis
  takes `LocalWitness …` directly; the `Nonempty (LocalWitness …)`
  wrapping is removed. Callers that previously relied on
  non-constructive nonemptiness now must produce explicit
  witnesses.
- `exists_sup_reduction_of_cover`: drops the unused
  `_hδ : 0 < δ` and `_hε : 0 < ε` arguments.
- `exists_sup_reduction`: drops the unused `_hm_pos : 0 < m₀`
  argument.

#### Renamed

- `f_le_m0` → `f_le_m₀`.
- `eps_le_sum_saving` → `ε_le_sum_saving`.
- `sup_le_of_saving` → `csSup_range_le_of_pointwise_saving`.

#### Added

- `CombArg.Refinement.openInterval` — canonical
  `Subtype.val ⁻¹' Set.Ioo (c.val − r) (c.val + r)` shape on
  `unitInterval`. Replaces five inline duplications across
  `SpacedIntervals.lean` and `InitialCover.lean`.
- `CombArg.Refinement.ExtendResult` — private structure bundling
  one inductive step's output (`pr'`, `J_castSucc`, `σ_castSucc`,
  `σ_last`, `covers_i_star`). Replaces an ad-hoc 4-property
  `Subtype` and four standalone `extend_refinement_*` lemmas.
- `test/Smoke.lean` rewritten: a non-trivial `LocalWitness`
  construction on `f ≡ 1`, an end-to-end `exists_sup_reduction`
  invocation parameterized in `N`, and a `#print axioms` block on
  all three public theorems (regression guard against new axioms).
- `examples/MinimalUsage.lean` rewritten as a runnable worked
  example, parameterized in `N`.
- `docs/design-notes.md` §14 records the v0.2 decisions.

#### Removed (internal cleanup)

- `step_succ` (was `Refinement/Induction.lean`): the paper-faithful
  `Finset.min'`-internal variant was never invoked outside its own
  file. `step_succ_at` (the externally-parameterized variant) is
  the only step function the termination proof uses; `step_succ`
  was 30 lines of dead code.
- `extend_refinement_J_castSucc`, `extend_refinement_σ_castSucc`,
  `extend_refinement_σ_last`, `extend_refinement_covers`: the four
  helper lemmas now appear as named fields of `ExtendResult`.
- `_h_uncov : ¬ (ic.I i_star ⊆ ⋃ pr.J k')` argument from
  `step_succ_at`: bound but never consumed in the proof. (Caller
  in `exists_terminal_refinement_aux` retains its own copy of the
  hypothesis for downstream use.)

#### Changed (internal)

- `step_succ_at` now returns `ExtendResult` directly instead of a
  4-property `Subtype`. Callers access `result.pr'`,
  `result.J_castSucc`, etc. by named field instead of
  `result.property.2.2.1`-style projections.
- `CombArg/Witness.lean` import narrowed from
  `Mathlib.Topology.Instances.Real.Lemmas` to
  `Mathlib.Topology.MetricSpace.Defs` (smaller transitive dep
  tree; `Witness.lean` builds with ~1090 jobs vs ~1500+).

#### Unchanged

- All proof bodies for the combinatorial argument (cover
  construction, refinement induction, parity rescue, scalar
  bookkeeping) — only signatures are simplified.
- `#print axioms` for all public theorems: still
  `[propext, Classical.choice, Quot.sound]`.
- LoC: 2052 (v0.1.1) → 1848 (v0.2), a −204 line / −10% reduction
  in library size with zero loss of mathematical content.

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

[0.2.0]: https://github.com/MathNetwork/comb_arg/releases/tag/v0.2.0
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
