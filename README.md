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

## Using this library once the GMT side is formalized

Suppose a Lean formalization of the geometric-measure-theoretic
infrastructure for an Almgren–Pitts min-max construction has been
carried out — in particular, the Hausdorff measure of boundary
surfaces, the local-replacement construction (De Lellis–Tasnady's
Lemma 3.1 / Pitts replacement), and an admissible class of
sweepouts. This section describes how `CombArg` plugs into such a
formalization as the combinatorial step.

The library treats the GMT side as **abstract input**: it asks
for a `LocalWitness` at every near-critical parameter and gives
back a scalar sup reduction. The interface is project-agnostic —
the same `LocalWitness` shape works for any GMT formalization,
whether it's a one-off proof in a single repository or a
community-scale Mathlib extension.

### What the consumer supplies (per call)

1. A continuous boundary energy `f : unitInterval → ℝ` — the
   sweepout's energy as a function of the path parameter.
2. `m₀ : ℝ` with `m₀ = sSup (Set.range f)` — the sup of `f` (or
   the min-max level when the sweepout sits at it).
3. `N : ℕ` with `0 < N` — the near-criticality parameter; the
   library's quantitative output is `1/(4·N)`.
4. For every `t : unitInterval` with `f t ≥ m₀ − 1/N`, a
   `LocalWitness unitInterval f t (1 / (4 * (N : ℝ)))`.

### `LocalWitness` ↔ DLT Lemma 3.1 correspondence

| Field | What the GMT side produces |
|---|---|
| `neighborhood : Set unitInterval` | DLT's open interval `(a_i, b_i)` around `t` on which the local replacement saves energy. |
| `isOpen_neighborhood` + `t_mem` | Openness of the interval; the parameter `t` lies in it. |
| `replacementEnergy : unitInterval → ℝ` | Boundary energy of the **replaced** sweepout: `s ↦ ℋⁿ(∂Ω̃_s)`, where `Ω̃_s` is the consumer's sweepout with the replacement inserted at parameter `s`. |
| `replacementEnergy_continuous` | Continuity of `replacementEnergy` as a function of `s`. DLT treats this implicitly; usually follows from "the replaced sweepout depends continuously on the inserted parameter" + "Hausdorff measure depends continuously on the boundary". The consumer must discharge it. |
| `saving_bound` | The quantitative DLT 3.1 inequality `f s − replacementEnergy s ≥ 1/(4·N)` for every `s ∈ neighborhood`. The substantive non-combinatorial content. |

### What you get back

```lean
∃ (f' : unitInterval → ℝ) (S : Set unitInterval),
  {t | f t ≥ m₀ − 1/N} ⊆ S ∧        -- (coverage)
  (∀ t, f' t ≤ f t) ∧                 -- (a) pointwise dominance
  (∀ t, t ∉ S → f' t = f t) ∧         -- (b) localization
  sSup (Set.range f') ≤ m₀ − 1/(4N)   -- (c) sup reduction
```

A scalar competitor `f'` strictly undercutting `m₀` by `1/(4·N)`,
together with a modification set `S` (the union of the cover
pieces) so that `f' = f` outside `S` and `f' ≤ f` everywhere.

### Plugging into a min-max contradiction

If the admissible class `𝒜` has `m₀ = inf_{𝒜} sup` and the
sweepout `Ω` realizes the inf, the standard contradiction is
three steps:

1. Apply `CombArg.exists_sup_reduction` to obtain `f'` with
   `sSup (range f') ≤ m₀ − 1/(4N)`.
2. Lift `f'` back to a sweepout `Ω' ∈ 𝒜` — the GMT side does
   this. The `f' = f` off `S` guarantee usually makes the lift
   routine: `Ω'` agrees with `Ω` outside `S` and uses the local
   replacement inside.
3. `sup of Ω' < m₀ = inf_{𝒜} sup` contradicts the admissibility
   of `Ω'`.

The library handles step 1; steps 2 and 3 are domain-specific.

### Skeleton client code

```lean
import CombArg
import YourGMT  -- your formalization providing
                -- YourGMT.localWitness_of_DLT and
                -- YourGMT.lift_sweepout

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

Three identifiers carry the GMT-side responsibility:

- `YourGMT.choose_N` — pick `N` large enough that `1/(4N)` beats
  the contradiction window the admissible class requires.
- `YourGMT.localWitness_of_DLT` — the GMT formalization of DLT
  Lemma 3.1 (the substantive geometric work, returning a per-`t`
  `LocalWitness`).
- `YourGMT.lift_sweepout` — convert the scalar `f'` (with its
  modification set `S`) back to a sweepout in `𝒜`.

### Known friction

- **1D parameter space only.** Multi-parameter sweepouts
  (`unitInterval^m`, Almgren cycles) need the multi-parameter
  cover construction; planned for v0.3.
- **Output is scalar, not geometric.** The consumer receives
  `f'` with a sup bound and a modification set `S`; lifting back
  to a sweepout is the GMT side's work. The `f' = f` off `S`
  guarantee is designed to make this lift mechanical.
- **`replacementEnergy_continuous` is a GMT-side obligation.**
  DLT 3.1 outputs continuity implicitly via "continuous family of
  replacements"; the Lean-level proof obligation falls on the
  consumer.
- **Lean / Mathlib version pin.** `v4.30.0-rc2` + the Mathlib
  revision in `lake-manifest.json`. Bumps on either side may
  require coordination.
- **Axiom budget.** This library uses only the three standard
  foundational axioms. Standard Mathlib measure-theory work
  stays within the same three.

For a runnable end-to-end invocation on a trivial `f ≡ 1`, see
[`examples/MinimalUsage.lean`](examples/MinimalUsage.lean). The
client-code skeleton above is what an actual GMT-backed
instantiation would look like once the `YourGMT.*` stubs are
replaced with their real definitions.

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
