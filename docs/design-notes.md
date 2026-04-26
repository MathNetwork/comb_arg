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
need their own `OneDim`-style sister namespace; not done in v0.3.

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
