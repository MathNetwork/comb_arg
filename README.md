# CombArg — Almgren–Pitts Combinatorial Argument, Formalized in Lean 4

A Lean 4 formalization of the **combinatorial core** of the
Almgren–Pitts min-max argument: the cover-refinement step
underlying the existence of minimal hypersurfaces, extracted as a
self-contained metric-combinatorial theorem with no
geometric-measure-theoretic dependencies.

## What this library provides

A **two-tier architecture** for the 1D combinatorial argument.
Both tiers prove the same abstract scalar conclusion
(a `FiniteCoverWithWitnesses` on `unitInterval`); they differ in
whether they preserve the spacing / overlap structure that a
geometric modified-sweepout lift requires.

### Tier 1: structured DLT path — `CombArg.OneDim`

From a continuous `f : unitInterval → ℝ` with `m₀ = sSup (range f)`,
`N > 0`, and a `LocalWitness` at every `1/N`-near-critical
parameter (saving `1/(4N)` each), the DLT §3.2 Step 1 algorithm
produces:

- **`CombArg.OneDim.exists_DLTCover`** — a structured
  `DLTCover f m₀ N` packaging the Stage A initial cover (with
  skip-2 spacing condition (a)), the Stage B partial refinement,
  σ-injectivity, and the termination invariant `∀ i, ic.I i ⊆ ⋃ k,
  pr.J k`. This is the import target for future geometric
  consumers (DLT modified-sweepout via positive-measure overlap
  blending) under `CombArg.Geometric.*`.
- **`CombArg.OneDim.exists_refinement`** — the abstract scalar
  output, defined as `(exists_DLTCover ...).toFinite`. Returns a
  `FiniteCoverWithWitnesses unitInterval f m₀ (1/N) (1/(4N))`
  satisfying

    - **(I)** `f − E_l ≥ s_l` on each piece,
    - **(II)** every `t` lies in at most two pieces (two-fold overlap),
    - **(III)** `{t : f t ≥ m₀ − 1/N} ⊆ ⋃ pieces`.

  Signature unchanged from v0.3; existing consumers continue to
  work without modification.

### Tier 2: cheap scalar path — `CombArg.Scalar`

- **`CombArg.Scalar.exists_refinement_partition`** — the same
  abstract `FiniteCoverWithWitnesses` conclusion, proved by
  partition-by-endpoints: compactness of the near-critical set
  plus a finite open subcover, sorting interval endpoints to
  partition `unitInterval` into closed pieces of multiplicity ≤ 2,
  with per-piece witness selection and continuity-based extension
  to the closed piece.

This proof imports neither `OneDim/SpacedIntervals` nor
`OneDim/Induction`; the dependency graph confirms that the DLT
spacing/parity machinery is *not* required for the abstract
scalar conclusion. It is required for the geometric lift.
See `paper/sections/intro.tex` Remark 1.5 for the architectural
rationale.

### Sup-reduction bookkeeping corollary — `CombArg.exists_sup_reduction_of_cover`

From any `FiniteCoverWithWitnesses K f m₀ δ ε` on a compact
nonempty space `K` with `ε ≤ δ`, produce a competitor
`f' : K → ℝ` with `f' ≤ f` pointwise, `f' = f` outside the cover
support, and `sSup (range f') ≤ m₀ − ε`. Three-line scalar
arithmetic over the cover data; generic in `K`.

A one-parameter specialization `CombArg.exists_sup_reduction`
chains this with the DLT path: on `K = unitInterval` with
`(δ, ε) = (1/N, 1/(4N))`, given just the witness hypothesis it
produces the sup-reducing competitor directly.

This formalization corresponds to the combinatorial core
appearing in De Lellis–Tasnady (2013) §3.2 and analogous
developments in Pitts (1981), Colding–De Lellis (2003),
De Lellis–Ramic (2017), and Marques–Neves (2014).

## Status

- **Version**: 0.4.0 (April 2026).
- **License**: Apache 2.0.
- **Build**: `lake build` succeeds with no warnings; zero `sorry`.
- **Verification**: five public theorems
  (`exists_sup_reduction`, `exists_sup_reduction_of_cover`,
  `OneDim.exists_refinement`, `OneDim.exists_DLTCover`,
  `Scalar.exists_refinement_partition`) depend only on the three
  standard Lean 4 / Mathlib foundational axioms (`propext`,
  `Classical.choice`, `Quot.sound`). Run `lake exe combarg-audit`
  for a one-command health check (axiom audit + public-API
  listing); CI runs the same on every push.

## Quick start

```bash
git clone https://github.com/MathNetwork/comb_arg.git
cd comb_arg
lake exe cache get          # download Mathlib pre-compiled oleans (first run)
lake build                  # main library
lake build test             # smoke test + axiom audit
lake build examples         # worked example
lake exe combarg-audit      # one-command health check
lake exe combarg-skeleton   # emit a starter min-max-contradiction script
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

- `CombArg.OneDim.exists_DLTCover` — structured DLT-style
  cover output (Stage A + B intermediate state) on `unitInterval`.
- `CombArg.OneDim.exists_refinement` — the abstract scalar
  output of the DLT path, equal to `(exists_DLTCover …).toFinite`.
- `CombArg.Scalar.exists_refinement_partition` — alternative
  cheap proof of the abstract scalar theorem via
  partition-by-endpoints; dependency-graph independent of the
  DLT spacing / induction machinery.
- `CombArg.exists_sup_reduction_of_cover` — bookkeeping corollary,
  generic `K`.
- `CombArg.exists_sup_reduction` — one-parameter chained corollary
  (composes DLT path + bookkeeping).
- Input structures `FiniteCoverWithWitnesses` and `LocalWitness`.
- Structured output `OneDim.DLTCover` for geometric consumers.
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
- The DLT modified-sweepout lift `Ω'_t` from a `DLTCover`. The
  v0.4 architecture exposes the structured cover data
  (`CombArg/Geometric/` directory placeholder), but the actual
  blending construction is deferred.
- Multi-parameter applications `K = unitInterval^m`. The
  bookkeeping corollary is already generic in `K`; only an
  additional cover construction is needed.

## Lifting this library to the original min-max proof

Suppose the min-max setting from the literature has been
formalized in Lean — an admissible class `𝒜` of sweepouts, the
inf-sup characterization `m₀ = inf_{Ω ∈ 𝒜} sup f_Ω`, the local
replacement construction (De Lellis–Tasnady's Lemma 3.1 / Pitts
replacement), and the Hausdorff measure of boundary surfaces.
This section describes how the abstract declarations of `CombArg`
then **lift into the combinatorial step of the original proof**.

The library is the formal abstract version of the combinatorial
slice that Pitts (1981), Colding–De Lellis (2003),
De Lellis–Tasnady (2013), De Lellis–Ramic (2018), and
Marques–Neves (2014) each re-derive in their own notation. Its
four public declarations make no GMT references and stand for
the four pieces the literature recombines at every instantiation.
`LocalWitness K f t ε` carries the abstract per-parameter
local-reducer data. `exists_refinement` is the formal counterpart
of De Lellis–Tasnady §3.2 Step 1, the interval refinement that
turns a family of local witnesses on the near-critical set into
a finite cover with two-fold overlap. `exists_sup_reduction_of_cover`
is the formal counterpart of De Lellis–Tasnady §3.2 Step 2, the
scalar bookkeeping
that turns such a cover into a sup-reducing competitor. The
chained one-parameter step `exists_sup_reduction` composes these
two into a single call.

What the literature supplies in its prose, and what the min-max
setting must formalize on its side, is the data that turns these
abstract declarations into concrete proof artifacts. Concretely:
the continuous boundary energy
`f := Ω.boundaryEnergy : unitInterval → ℝ` of a sweepout `Ω`
realizing `m₀ = sup f`; a near-criticality parameter `N : ℕ`
chosen so that `1/(4N)` beats whatever contradiction window the
admissible class needs; and a local replacement lemma producing,
at every parameter `t` with `f(t) ≥ m₀ − 1/N`, a
`LocalWitness unitInterval f t (1/(4N))` whose four data fields
come from the GMT-side replacement family. The Lean declarations
of the library do not change between the abstract and
instantiated forms — they are exactly the same definitions
either way; what changes is that this min-max-side data flows in
as the inputs.

### The instantiation: `LocalWitness` from the local replacement lemma

The `LocalWitness` structure was designed to be the data shape
that the De Lellis–Tasnady local replacement lemma
([DLT13] Lemma 3.1) produces, with each field naming a specific
piece of the GMT-side replacement data. The open interval
`(a_i, b_i) ⊆ [0,1]` on which the local replacement saves
energy becomes the `neighborhood` field; the boundary energy of
the replaced sweepout, `s ↦ ℋⁿ(∂Ω̃_s)`, becomes
`replacementEnergy`; its continuity in `s` (which the local
replacement lemma treats implicitly through the continuity of
the replaced family in the inserted parameter) becomes the
`replacementEnergy_continuous` obligation that the GMT side
must discharge explicitly; and the quantitative inequality
`f(s) − ℋⁿ(∂Ω̃_s) ≥ 1/(4N)` on `(a_i, b_i)` becomes
`saving_bound`. The full mapping:

| Library field | The corresponding piece of the original proof |
|---|---|
| `neighborhood : Set unitInterval` | The open interval `(a_i, b_i) ⊆ [0,1]` around `t`. |
| `isOpen_neighborhood` + `t_mem` | Openness of the interval; the parameter `t` lies in it. |
| `replacementEnergy : unitInterval → ℝ` | `s ↦ ℋⁿ(∂Ω̃_s)`, the boundary energy of the replaced sweepout. |
| `replacementEnergy_continuous` | Continuity of `s ↦ ℋⁿ(∂Ω̃_s)` in `s`. |
| `saving_bound` | The quantitative inequality `f(s) − ℋⁿ(∂Ω̃_s) ≥ 1/(4N)` for `s ∈ (a_i, b_i)`. |

### The proof chain: from sup reduction to contradiction

With this data in place, `CombArg.exists_sup_reduction` returns
the existential

```lean
∃ (f' : unitInterval → ℝ) (S : Set unitInterval),
  {t | f t ≥ m₀ − 1/N} ⊆ S ∧        -- (coverage)
  (∀ t, f' t ≤ f t) ∧                 -- (a) pointwise dominance
  (∀ t, t ∉ S → f' t = f t) ∧         -- (b) localization
  sSup (Set.range f') ≤ m₀ − 1/(4N)   -- (c) sup reduction
```

which is, definitionally, the sup-reduction step the original
proof uses. The competitor `f'` and modification set `S` are the
formal images of "the sweepout's energy after the local
replacements have been combined"; conditions (a) and (b) anchor
`f'` to `f` so that `f'` is a genuine combinatorial reduction
rather than a trivial constant.

The literature now closes the proof by lifting `f'` back to a
sweepout `Ω' ∈ 𝒜` and contradicting the inf-sup. In Lean this
chain has three pieces, of which the library discharges the
first: `exists_sup_reduction` produces `f'` with
`sSup (range f') ≤ m₀ − 1/(4N)`. The min-max setting then
discharges the second by taking `f'` together with its
modification set `S` back to a sweepout `Ω' ∈ 𝒜` — the (b)
localization guarantee makes this lift mechanical, since `Ω'`
agrees with `Ω` outside `S` and inserts the local replacement on
each piece of `S`. The contradiction follows immediately from
`sup f_{Ω'} ≤ m₀ − 1/(4N) < m₀ = inf_{𝒜} sup` together with
`Ω' ∈ 𝒜`. Together with the library's first piece, these
reconstruct line for line the literature's contradiction chain.

### Skeleton client code

The pattern below shows what the chain looks like when assembled
end to end, with `YourGMT.*` stubs standing in for the GMT-side
declarations a min-max formalization would supply:

```lean
import CombArg
import YourGMT

theorem minmax_contradiction
    (Ω : YourGMT.SweepoutType) (hΩ : Ω ∈ YourGMT.admissibleClass)
    (h_minmax : Ω.boundaryEnergy.sup = YourGMT.infMinmax) :
    False := by
  set f := Ω.boundaryEnergy
  set m₀ := sSup (Set.range f)
  obtain ⟨N, hN_pos, hN_window⟩ := YourGMT.choose_N Ω
  -- The Lean image of DLT Lemma 3.1: per-parameter local witness.
  have witness : ∀ t : unitInterval, f t ≥ m₀ - 1 / (N : ℝ) →
                   LocalWitness unitInterval f t (1 / (4 * (N : ℝ))) :=
    fun t ht => YourGMT.localWitness_of_DLT Ω t ht hN_pos
  -- comb-arg: combinatorial bookkeeping → scalar sup reduction.
  obtain ⟨f', S, _, h_le, h_eq, h_sup⟩ :=
    CombArg.exists_sup_reduction Ω.boundaryEnergyContinuous rfl hN_pos witness
  -- Lift f' back to a sweepout in 𝒜.
  obtain ⟨Ω', hΩ', hΩ'_energy⟩ :=
    YourGMT.lift_sweepout f' h_le h_eq Ω hΩ
  -- Contradiction with the inf-sup characterization of m₀.
  have h_lt : Ω'.boundaryEnergy.sup < m₀ := by
    rw [hΩ'_energy]; linarith [h_sup, hN_window]
  exact absurd h_lt (YourGMT.le_of_admissible hΩ' h_minmax)
```

The three `YourGMT.*` identifiers mark the GMT-side
responsibility: `YourGMT.choose_N` picks `N` so that `1/(4N)`
beats the admissible class's contradiction window;
`YourGMT.localWitness_of_DLT` is the GMT formalization of the
local replacement lemma ([DLT13] Lemma 3.1), returning a
per-`t` `LocalWitness`; and
`YourGMT.lift_sweepout` converts the scalar `f'` (with its
modification set `S`) back to a sweepout in `𝒜`.

### Known friction

The library is currently specialized to the 1D parameter space
`unitInterval`; multi-parameter sweepouts (`unitInterval^m`, in
particular Almgren cycles) will need a multi-parameter cover
construction, scheduled post-v0.4. The output through
`exists_sup_reduction` is scalar rather than geometric — the
consumer receives `f'` with its sup bound and the modification set
`S`, and must lift back to a sweepout in `𝒜` on the GMT side;
the `f' = f` off `S` guarantee is designed to make this lift
mechanical. For a structured cover with the spacing / overlap
data that supports a DLT-style modified-sweepout lift directly,
import `CombArg.OneDim.exists_DLTCover` instead — the v0.4
two-tier architecture exposes this object as a first-class
import target (the `Geometric/` directory placeholder marks the
position the future lift implementation occupies). Continuity of
`replacementEnergy` in the inserted parameter falls on the
consumer to discharge explicitly, since the local replacement
lemma supplies it only implicitly through the continuity of the
replaced family. The library is pinned to
`leanprover/lean4:v4.30.0-rc2` plus the Mathlib revision in
`lake-manifest.json`, so bumps on either side may require
coordination. The library itself uses only the three standard
foundational axioms (`propext`, `Classical.choice`, `Quot.sound`),
and standard Mathlib measure-theory work stays within the same
three.

For a runnable end-to-end invocation on a trivial `f ≡ 1`, see
[`examples/MinimalUsage.lean`](examples/MinimalUsage.lean). The
client-code skeleton above is what an actual GMT-backed
instantiation would look like once the `YourGMT.*` stubs are
replaced with their real definitions.

## Public API stability

The following names are considered stable public API and will not
change without a major version bump:

- `CombArg.OneDim.exists_DLTCover`
- `CombArg.OneDim.exists_refinement`
- `CombArg.Scalar.exists_refinement_partition`
- `CombArg.exists_sup_reduction_of_cover`
- `CombArg.exists_sup_reduction`
- `CombArg.FiniteCoverWithWitnesses` (structure + fields)
- `CombArg.LocalWitness` (structure + fields)
- `CombArg.OneDim.DLTCover` (structure + fields)
- `CombArg.OneDim.InitialCover` (structure + fields)
- `CombArg.OneDim.PartialRefinement` (structure + fields)
- `CombArg.OneDim.SkippedSpacedIntervals` (structure + fields)
- `CombArg.OneDim.nearCritical`
- `CombArg.OneDim.openInterval`

Internal definitions (`step_succ_at`, `ExtendResult`, the
internal partition-construction helpers in `Scalar/Partition`,
chain-spacing lemmas, etc.) may change in minor releases.

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
│   ├── Witness.lean           LocalWitness
│   ├── Cover.lean             FiniteCoverWithWitnesses +
│   │                          exists_sup_reduction_of_cover
│   ├── SupReduction.lean      exists_sup_reduction
│   ├── OneDim.lean            facade for the DLT-style tier
│   ├── OneDim/                tier 1: structured DLT path
│   │   ├── SpacedIntervals.lean     openInterval +
│   │   │                            SkippedSpacedIntervals
│   │   ├── InitialCover.lean        nearCritical + InitialCover
│   │   ├── CoverConstruction.lean   exists_initialCover
│   │   ├── PartialRefinement.lean   mid-induction state
│   │   ├── Induction.lean           step_succ_at +
│   │   │                            exists_terminal_refinement
│   │   ├── DLTCover.lean            structured Stage A+B output
│   │   └── Assembly.lean            exists_DLTCover +
│   │                                exists_refinement
│   ├── Scalar.lean            facade for the cheap-proof tier
│   ├── Scalar/                tier 2: alternative scalar path
│   │   └── Partition.lean           exists_refinement_partition
│   └── Geometric/             placeholder for future GMT lift
│       └── README.md
├── Audit.lean                 lake exe combarg-audit (axiom audit)
├── Skeleton.lean              lake exe combarg-skeleton
├── docs/
│   ├── project-overview.md    narrative tour
│   └── design-notes.md        design decisions + findings
├── paper/                     LaTeX writeup (Remark 1.5
│                              motivates the two-tier design)
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
