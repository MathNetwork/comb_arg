# Changelog

All notable changes to CombArg will be documented here.
Format based on [Keep a Changelog](https://keepachangelog.com/).

## [0.4.0] — 2026-04-28

### Two-tier architecture: structured DLT cover + alternative scalar proof

A purely-additive architectural pass. The DLT-style construction is
factored into a first-class structured output `OneDim.DLTCover` so
that a future geometric consumer (DLT modified-sweepout via positive-
measure overlap blending) has a stable import target carrying the
full Stage A + B intermediate state. In parallel, the abstract scalar
theorem is given a second, strictly cheaper proof
(`Scalar.exists_refinement_partition`) by partition-by-endpoints,
making it machine-verifiable that the DLT machinery is *not*
arithmetically required for the abstract `FiniteCoverWithWitnesses`
output --- it is required for the geometric lift, which is where the
construction's overlap structure actually load-bears.

Existing consumers (`exists_sup_reduction`,
`exists_sup_reduction_of_cover`, `OneDim.exists_refinement`) are
**unchanged in signature** and continue to work without modification.

#### Added (Lean)

- **`CombArg/OneDim/DLTCover.lean`** — new structured output type
  `DLTCover f m₀ N` packaging the Stage A initial cover (with skip-2
  spacing condition (a)), the Stage B partial refinement, the
  termination invariant `∀ i, ic.I i ⊆ ⋃ k, pr.J k`, and
  σ-injectivity. Convenience projections `J k`, `σ k`, `wit k`;
  derived lemmas `saving_on_J`, `saving_bound_closure`,
  `twoFold_closure`, `covers_nearCritical`; downgrade
  `toFinite : DLTCover → FiniteCoverWithWitnesses`.
- **`CombArg.OneDim.exists_DLTCover`** — the structured version of
  the combinatorial main theorem. Chains
  `exists_initialCover` and `exists_terminal_refinement` and
  packages their output into `DLTCover`. Public API.
- **`CombArg/Scalar/Partition.lean`** + **`CombArg.Scalar`** facade
  — alternative cheap proof of the abstract scalar theorem via
  partition-by-endpoints. Compactness of the near-critical set
  yields a finite open subcover, sorting interval endpoints
  partitions `unitInterval` into closed pieces of multiplicity ≤ 2,
  and continuity extends per-piece saving from the open `Ioo`
  interior to the closed piece. The proof imports neither
  `OneDim/Induction` nor `OneDim/SpacedIntervals` --- the
  dependency graph confirms that the DLT spacing/parity machinery
  is *not* required for the abstract scalar conclusion.
- **`CombArg/Geometric/`** — directory placeholder for future
  geometric consumers; a `README.md` notes that v0.4 ships only
  the architecture, with the actual modified-sweepout lift
  (`ModifiedSweepout.lean`) deferred.

#### Changed (Lean — internal refactor, public API unchanged)

- `OneDim/Assembly.lean` is now thin: `exists_DLTCover` (Stage A +
  Stage B → `DLTCover`) plus a re-defined `exists_refinement` as
  `(exists_DLTCover ...).toFinite`. The `terminal_twoFold` and
  `saving_bound_closure` lemmas previously inline in Assembly
  migrate into `DLTCover` as methods on the structured output.
  The output of `exists_refinement` is bit-identical to v0.3.

#### Added (audit + tests)

- **`Audit.lean`** now audits five public theorems
  (`exists_sup_reduction`, `exists_sup_reduction_of_cover`,
  `OneDim.exists_refinement`, `OneDim.exists_DLTCover`,
  `Scalar.exists_refinement_partition`); all five depend only on
  `propext`, `Classical.choice`, `Quot.sound`. The public-API
  listing grows from 4 to 8 declarations (adding `DLTCover`,
  `exists_DLTCover`, `exists_refinement_partition`).
- **`test/Smoke.lean`** adds an end-to-end invocation of
  `Scalar.exists_refinement_partition` and `#print axioms`
  guards on `exists_DLTCover` and `exists_refinement_partition`.

#### Found (paper-level)

- **F5. The two-tier architecture is verified, not asserted.** Paper
  Remark 1.5 (`rem:why-construction`) claims that the abstract
  scalar Theorem 1.3 admits a strictly shorter proof and that the
  DLT machinery is over-engineered at the abstract level. v0.4
  upgrades this from prose claim to dependency-graph fact:
  `Scalar/Partition.lean` ships a complete, sorry-free, axiom-clean
  proof of the same conclusion that imports none of the DLT-side
  refinement machinery. The DLT path's value lies entirely in
  preserving structure (spacing, σ-injectivity, J_subset) for a
  geometric lift --- the new `DLTCover` output is the import target
  that future geometric consumers will use.

## [0.3.0] — 2026-04-26

### Restructure for clarity + developer-tooling pass

A second-pass cleanup that reorganizes modules along the K-generic
vs. 1D-specialized boundary, eliminates dead wrapper files,
introduces Mathlib-style annotations and a Lean 4 `extends`-based
inheritance, and adds two `lake exe` targets plus a CI workflow
for end-to-end automation. **Breaking** changes are confined to
file paths and a small number of namespace renames.

#### Changed (breaking — file paths)

- `CombArg/Core.lean` → `CombArg/Cover.lean` (renamed for
  semantic accuracy: this file holds the `FiniteCoverWithWitnesses`
  structure and the K-generic bookkeeping corollary).
- `CombArg/Refinement.lean` → `CombArg/OneDim.lean` (facade).
- `CombArg/Refinement/*` → `CombArg/OneDim/*` (every submodule):
  `SpacedIntervals`, `InitialCover`, `CoverConstruction`,
  `PartialRefinement`, `Induction`, `Assembly`. The new directory
  name `OneDim/` flags the 1D-specialized character of the cover
  construction; the K-generic content lives at top level.
- `CombArg.Refinement.exists_refinement` → `CombArg.OneDim.exists_refinement`.

#### Removed

- `CombArg/Refinement/Disjointness.lean` (81 lines). All four
  lemmas were one-line wrappers delegating to the
  `SkippedSpacedIntervals` projection; Assembly already called
  the projection form directly, so the wrapper file was dead.
- `CombArg/Util.lean` (48 lines). Two utility lemmas relocated
  inline as `private` lemmas: `ge_of_closure_of_ge` into
  `CombArg/OneDim/Assembly.lean` (its only consumer);
  `exists_even_gap_of_three` into `CombArg/OneDim/SpacedIntervals.lean`
  (its only consumer).

#### Changed (internal)

- `InitialCover` now `extends SkippedSpacedIntervals`. The shared
  geometric fields (n, intervalCenter, radius, radius_pos,
  two_fold_spacing) come from the parent; the manual
  `toSkippedSpacedIntervals` projection definition and the
  `toSkippedSpacedIntervals_I` reflexivity lemma are auto-generated
  and so removed from source.
- `InitialCover.I` becomes a one-line `@[reducible] def`
  delegating to `ic.toSkippedSpacedIntervals.I`.

#### Added (annotations)

- `@[ext]` on `LocalWitness`, `FiniteCoverWithWitnesses`,
  `SkippedSpacedIntervals`, `InitialCover`. Auto-generates
  extensionality lemmas.
- `@[simp]` on `mem_nearCritical` (joining the existing
  `@[simp] mem_piecesContaining`).

#### Added (tooling)

- **`lake exe combarg-audit`** (Audit.lean). One-command health
  check: imports the library, walks the proof terms of the three
  public theorems via `Environment.find?` + `Expr.foldConsts`,
  and verifies the foundational axioms reduce to exactly
  `{propext, Classical.choice, Quot.sound}`. Prints the public-API
  listing alongside. Exit 0 on healthy, 1 on any audit failure.
  Suitable for both interactive use and CI invocation.
- **`lake exe combarg-skeleton`** (Skeleton.lean). Client-template
  generator: emits a starter min-max contradiction Lean script
  with `YourGMT.*` placeholder identifiers that a downstream
  geometric formalization fills in. CLI options
  `--N <name>` (parameter-variable name) and `--module <name>`
  (wrap in namespace).
- **`scripts/build-graph.sh`** + `docs/import-graph.{dot,svg}`.
  Module dependency graph generated via Mathlib's `importGraph`
  package; SVG suitable for embedding in README.
- **GitHub Actions CI workflow** (`.github/workflows/ci.yml`).
  On every push and PR: `lake build`, `lake build test`,
  `lake build examples`, sorry/admit grep, foundational-axiom
  audit (3 public theorems), and `lake exe combarg-audit`.

#### Added (testing)

- `test/Smoke.lean` gains a §3 invocation of
  `exists_sup_reduction_of_cover` on `K = Fin 2`, with a
  hand-built `FiniteCoverWithWitnesses`. Confirms the K-generic
  bookkeeping path does not silently depend on `unitInterval`
  specifics.

#### Unchanged

- All proof bodies for the combinatorial argument.
- `#print axioms` for all public theorems: still
  `[propext, Classical.choice, Quot.sound]`.
- LoC: 1848 (v0.2) → ~1700 (v0.3) before tooling files; with
  Audit.lean + Skeleton.lean tooling added, the net effective
  library code is even smaller.

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

[0.3.0]: https://github.com/MathNetwork/comb_arg/releases/tag/v0.3.0
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
