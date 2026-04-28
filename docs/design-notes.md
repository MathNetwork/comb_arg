# Design notes

This file records the **load-bearing design choices** of `CombArg`
and the **mathematical findings** the formalization surfaced. The
historical record of removed scaffolding (the `PairableCover`
typeclass scrapped in v0.2, the v0.1 → v0.1.1 reframe, the v0.3
restructure) lives in [`CHANGELOG.md`](../CHANGELOG.md); this file
keeps only the current rationale and the findings worth flagging
to a downstream reader.

## Design choices

### 1. Reduction form, not contradiction form

The top-level theorem `CombArg.exists_sup_reduction` produces a
strictly-better competitor `f'` (reduction form), not a `False`
conclusion contradicting some inf-sup characterization
(contradiction form). The contradiction form would require
importing an admissible-class / min-max-level hypothesis, which in
turn requires GMT structure and breaks the project's standalone
scope. Downstream users with their own admissible-class framework
layer the contradiction on top of the reduction (see
[`paper/sections/integration.tex`](../paper/sections/integration.tex)
§4.2 for the explicit chain).

### 2. Parameter space `K = unitInterval`

The combinatorial main theorem (`CombArg.OneDim.exists_refinement`)
is specialized to `K = unitInterval`. The bookkeeping corollary
(`CombArg.exists_sup_reduction_of_cover`) is generic in `K`. The
specialization is in the `OneDim/` directory; the `K`-generic
content lives at the top level.

Multi-parameter cover constructions
(`K = unitInterval^m`, Almgren cycles) fit the same pattern but
need their own `OneDim`-style sister namespace; not done as of v0.4.

### 3. `LocalWitness` exposes only the replacement *energy*, not a family

`LocalWitness K f t ε` carries a continuous
`replacementEnergy : K → ℝ` and a quantitative saving inequality;
it does **not** carry a concrete replacement family `K → X` in
some ambient geometric space `X`. This keeps the combinatorial
theorem agnostic to how the replacement is realized: a downstream
GMT formalization wires its own geometric replacement family in
behind the `replacementEnergy` scalar.

The `replacementEnergy_continuous` field is the only obligation
treated implicitly in the literature (continuity of the replaced
family in the inserted parameter is folded into the prose); the
formalization makes it an explicit obligation on the witness
producer.

### 4. Narrow per-file imports

Each module imports the narrowest Mathlib path it actually needs.
For example, `CombArg/Witness.lean` imports
`Mathlib.Topology.MetricSpace.Pseudo.Defs` rather than the much
larger `Mathlib.Topology.Instances.Real.Lemmas`. The savings
compound across the dependency graph; cleaner error messages
trace back to a single missing identifier when an import is
missing.

### 5. Two-tier architecture: DLT path vs cheap scalar path

The library ships two separate proofs of the same abstract
scalar conclusion (`FiniteCoverWithWitnesses unitInterval f m₀
(1/N) (1/(4N))`):

- **Tier 1 — `CombArg/OneDim/`** (the DLT path) follows De
  Lellis–Tasnady §3.2 Step 1 faithfully: Lebesgue-number cover,
  smallest-index refinement induction with set-difference Case 2,
  parity-rescue closure two-fold, σ-injectivity. Its structured
  output `DLTCover` exposes the Stage A initial cover + Stage B
  partial refinement + invariants for downstream geometric
  consumers.
- **Tier 2 — `CombArg/Scalar/Partition.lean`** is a strictly
  cheaper alternative: compactness gives a finite open subcover,
  sorting all interval endpoints partitions `unitInterval` into
  closed pieces of multiplicity ≤ 2, witness selection per piece
  is by direct Classical choice, saving extends to the closed
  piece by continuity. This proof imports neither
  `OneDim/SpacedIntervals` nor `OneDim/Induction` — the
  dependency graph confirms that the DLT spacing/parity machinery
  is *not* arithmetically required for the abstract scalar
  conclusion.

The `Scalar/` tier is *not* a replacement for the DLT path. It
delivers the same `FiniteCoverWithWitnesses` output but discards
the spacing / overlap / σ-injectivity structure that the
geometric modified-sweepout lift will need (DLT's blending in
`J_i ∩ J_{i+1}` requires positive-measure overlap; a partition's
measure-zero endpoint sharing breaks t-continuity of the lifted
sweepout). The DLT path is the import target for
`CombArg/Geometric/`; the Scalar path is the import target for
consumers who only need the abstract scalar bound.

The two tiers are **strictly separated** in the dependency graph
(see Finding F7): a `lake build CombArg.Scalar.Partition` compiles
zero `OneDim/*` files. Both tiers consume the shared `nearCritical`
definition from `CombArg.Common.NearCritical` (extracted in v0.5
specifically to remove the last cross-tier dependency); both
consume the input/output types `LocalWitness` (`Witness.lean`)
and `FiniteCoverWithWitnesses` (`Cover.lean`).

This is recorded as **Finding F5** below and elaborated in
`paper/sections/intro.tex` Remark 1.5 (`rem:why-construction`).

### 6. Set-theoretic, not smooth

The combinatorial argument (and DLT's geometric lift) is expressed
in terms of *raw set operations* — open intervals, set differences,
closures, unions, multiplicity counts — and the Lean formalization
mirrors this exactly. There is no use of bump functions, smooth
partitions of unity, mollifiers, or differential forms anywhere in
`CombArg/`. The continuity used is plain topological continuity;
the saving estimate is pointwise.

The DLT modified-sweepout blending formula

```
Ω'_t = [Ω_t \ (U_i' ∪ U_{i+1}')] ∪ [Ω_{i,t} ∩ U_i']
                                  ∪ [Ω_{i+1,t} ∩ U_{i+1}']
```

is itself a pure set-algebraic expression in `Ω_t` and the
replacements; t-continuity comes from continuity of the input
families `Ω_t`, `Ω_{i,t}` plus the t-independence of the cut
sets `U_i'`, not from any smoothness of cut-off weights. The
v0.4 `Geometric/` placeholder will inherit this convention.

A smoothed alternative (replacing each piece by a smooth bump
`ρ_k` with `supp ρ_k ⊆ U_k` and blending by weighted average)
is *possible* but not faithful to DLT and would require lifting
the saving estimate through the multiplier inequality. Set-based
data is the more flexible primitive: a downstream consumer who
wants smooth partition-of-unity data can always derive bump
functions from open-set pieces (Mathlib provides this), whereas
recovering pointwise saving from a multiplier-blurred saving is
not direct.

## Findings the formalization surfaced

These are paper-level observations about the De Lellis–Tasnady
combinatorial argument that the formalization exposed and that the
prose in the literature compresses. Each one is a place where the
Lean proof carries structure the prose treats as obvious. They are
catalogued at greater length in
[`paper/sections/proof.tex`](../paper/sections/proof.tex) and
under §11 of this file's history.

### F1. Witness threshold is `1/(4N)` exactly, not `∃ε > 0`

The witness hypothesis must commit to `ε = 1/(4N)` exactly, not
the weaker existential form `∃ ε > 0, …`. Lemma 3.1
of~\[DLT13\] outputs this specific value, and the cover-refinement
induction maintains `1/(4N)` as a uniform invariant; an
existential `ε` does not thread through the induction without
adding extra arithmetic that the paper's proof simply does not
do.

### F2. Interval center and witness center must be separated

The De Lellis–Tasnady paper's `t_i` plays two roles in Step 1's
opening sentence: it is both the *center* of the interval `I_i`
(in spacing condition (a)) and the *base* at which the witness
neighborhood `η_{t_i}` is taken (in condition (b)). Forcing those
two roles to be the same point makes the existence proof for
`InitialCover` intractable through the standard Lebesgue-number
construction: Lebesgue gives a uniform `λ > 0` such that every
`λ`-ball around an `NC` point sits inside *some* witness
neighborhood, but the witness neighborhood need not be centered
at that point. The formalization decouples the two roles
(`intervalCenter i` vs `witnessCenter i`, linked by
`I_subset_neighborhood`) and recovers the paper's downstream
induction.

### F3. The smallest-index map `σ` is not monotone

The induction in DLT §3.2 picks the "smallest index" not yet
processed; the geometric intuition (process left-to-right)
suggests `σ : Fin l → Fin n` is monotone on the partial
refinement. The formalization shows it is not. After Case 2 of
`step_succ_at` truncates an interval, the next step's
smallest-index choice can pick an index *less than*
`σ(prev)` if an earlier index was skipped because its
containment-or-truncation predicate was not yet checked. The
weaker invariant the proof actually maintains is
`Function.Injective σ`, derivable from `processed_cover` and
threaded explicitly through `exists_terminal_refinement`.

### F4. Even-gap-only disjointness needs a parity rescue for two-fold

Spacing condition (a) constrains pairs `(i, i+2)` only. The chain
lemma `chain_spacing` extends this to *even-gap* pairs `(i, j)`
with `j.val - i.val = 2(m+1)`; **odd-gap pairs are not constrained
at all** (an explicit numerical counter-example with monotone
centers and chosen radii produces an odd-gap intersection). The
paper's one-sentence claim "every point lies in at most two
`J_l`'s" (Lemma 3.2) therefore does not follow directly from
spacing (a); it needs the parity argument

> Among any three distinct sorted indices `a < b < c`,
> some pair has even gap `≥ 2`.

The Lean proof spells this out as
`exists_even_gap_of_three` (an `omega`-discharged integer fact)
combined with `closure_disjoint_of_even_gap`. This three-layer
structure is invisible at the prose level but inescapable in the
formalization.

### F5. Two-tier verification: paper Remark 1.5 is dependency-graph fact

Paper Remark 1.5 (`rem:why-construction`) claims that the abstract
scalar Theorem 1.3 admits a strictly shorter proof, and that the
DLT spacing / refinement / parity machinery is *over-engineered*
relative to the abstract scalar conclusion alone — its value lies
in producing structure that the geometric lift consumes.

In v0.4 this claim is upgraded from prose to dependency-graph
fact. `CombArg/Scalar/Partition.lean` ships a complete, sorry-free,
axiom-clean proof of the same `FiniteCoverWithWitnesses`
conclusion as `OneDim/Assembly.exists_refinement`, and its
imports (`CombArg.Cover`, `CombArg.Witness`,
`CombArg.OneDim.InitialCover` for the `nearCritical` definition,
plus standard Mathlib) deliberately exclude
`OneDim/SpacedIntervals`, `OneDim/PartialRefinement`,
`OneDim/Induction`, and `OneDim/Assembly`. A `lake build
CombArg.Scalar.Partition` confirms the Scalar tier is
self-sufficient.

Symmetrically, `OneDim.exists_DLTCover` (the structured form)
exposes the spacing / refinement / σ-injectivity data that the
abstract `FiniteCoverWithWitnesses` collapses into a plain
multiplicity bound; a future `CombArg/Geometric/ModifiedSweepout`
consuming `DLTCover` will use this preserved structure, while a
consumer of the Scalar tier cannot reconstruct it.

### F6. The combinatorial argument is set-theoretic, not smooth

This is closer to a confirmation than a finding: every theorem in
`CombArg/` is expressed and proved using only topological-set
primitives (open / closed / closure / Ioo / Icc / set difference)
plus pointwise continuity. No bump functions, mollifiers, smooth
partitions of unity, or differential forms appear anywhere. The
continuity used in the saving-extension argument
(`saving_bound_closure`, `mem_closure_val_preimage_Ioo`) is just
`Continuous f` plus `IsClosed.closure_subset_iff` for the
sub-level set `{s | c ≤ g s}`.

The DLT geometric lift inherits this convention: the modified
sweepout `Ω'_t = [Ω_t ∖ (U_i' ∪ U_{i+1}')] ∪ ...` is a pure
set-algebraic expression in `Ω_t` and the replacements, and its
t-continuity comes from continuity of the input GMT families plus
t-independence of the cut sets `U_i'` — no smoothness of weights
needed. The `Geometric/` placeholder will keep to this convention.

See design choice §6 above for the comparison with a smoothed
alternative.

### F7. Two-tier dependency-graph separation is strict, not approximate

In v0.4, paper Remark 1.5 (`rem:why-construction`) and design
choice §5 above asserted that the `OneDim/` (DLT path) and
`Scalar/` (cheap path) tiers are dependency-graph independent.
This was *almost* true: `Scalar/Partition/CoverIvl.lean` imported
`CombArg.OneDim.InitialCover` solely for the `nearCritical`
definition, not for any of `OneDim`'s spacing / induction / parity
machinery, but the import statement itself created a soft
violation.

In v0.5 the `nearCritical` set together with its closedness,
compactness, and non-emptiness lemmas were extracted to
`CombArg/Common/NearCritical.lean`. After the move,
`Scalar/Partition/CoverIvl.lean` imports
`CombArg.Common.NearCritical` (not any `OneDim/*` file), and
`OneDim/InitialCover.lean` likewise imports the shared `Common`
definition. The dependency graph is now strictly separated:

```text
$ lake build CombArg.Scalar.Partition
…
✔ Built CombArg.Cover
✔ Built CombArg.Witness
✔ Built CombArg.Common.NearCritical
✔ Built CombArg.Scalar.Partition.Helpers
✔ Built CombArg.Scalar.Partition.CoverIvl
✔ Built CombArg.Scalar.Partition.Endpoints
✔ Built CombArg.Scalar.Partition.Pieces
✔ Built CombArg.Scalar.Partition.WitnessSelection
✔ Built CombArg.Scalar.Partition.Multiplicity
✔ Built CombArg.Scalar.Partition.Coverage
✔ Built CombArg.Scalar.Partition
```

Zero `OneDim/*` modules compile when the partition route is
isolated. The architectural claim Remark 1.5 makes about the
two tiers is therefore upgraded from "almost separated" to
"strictly separated, mechanically verified by `lake build`."

The public API name `CombArg.OneDim.nearCritical` is preserved
(the new `Common/NearCritical.lean` uses `namespace
CombArg.OneDim` for the moved declarations) so the README's
stable-API list remains valid without modification.
