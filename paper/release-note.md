# Release note — CombArg v0.1.0

> **Note (2026-04-25).** This release note documents the v0.1.0 state.
> v0.1.1 reframed the main theorem (combinatorial core vs. bookkeeping
> corollary) and v0.2 simplified the public API (removed
> `PairableCover`, the ambient space `X`, the `Nonempty`-wrapping of
> `LocalWitness`, and several unused hypotheses). For the current
> public signatures, see `README.md` and `CHANGELOG.md`. The known
> limitations below labelled "v0.1" are largely resolved in v0.2.

**Accompanying paper:** *Compiling the Almgren–Pitts Combinatorial Argument*.
**Library:** CombArg v0.1.0, Apache-2.0,
<https://github.com/MathNetwork/comb_arg>.
**Release date:** 2026-04-23.

## What this release is

The Almgren–Pitts combinatorial argument — the quantitative
covering-refinement argument that appears as Step 2 of min-max
constructions of minimal hypersurfaces in Pitts (1981),
Colding–De Lellis (2003), De Lellis–Tasnady (2013), De Lellis–Ramic
(2017), De Lellis (Annales Fourier, 2016), Marques–Neves (2014),
and subsequent literature — extracted from its
geometric-measure-theory context and released as a standalone
machine-verified theorem in Lean 4.

The main theorem, `CombArg.exists_sup_reduction`, asserts that
given a continuous energy `f : unitInterval → ℝ` with supremum `m₀`,
a near-criticality parameter `N > 0`, and a local reducer witness
with saving `1/(4N)` at every `1/N`-near-critical parameter, there
exists a modified function `f'` with `sSup (range f') ≤ m₀ − 1/(4N)`.

The library depends only on the three standard Lean 4 foundational
axioms (`propext`, `Classical.choice`, `Quot.sound`) and `Mathlib`'s
real analysis and topology. No project-local axioms. No `sorry`.

## What this release is not

It is not a new mathematical result. The argument follows the
argument structure of De Lellis–Tasnady (2013) §3.2, abstracted
from its geometric-measure-theoretic instantiation. The
contribution is a form transformation: the combinatorial step is
now importable as a library rather than re-derived in each
successor paper.

It is not a full min-max formalization. The library covers the
combinatorial core only. The local-replacement lemma (step 1 of the
min-max pattern) and the admissible-class argument (step 3) remain
the consumer's responsibility.

Whether this material should migrate to Mathlib, and in what form,
is not addressed here.

## Why it might matter

For authors of future min-max constructions: the combinatorial step
becomes a one-line citation. For GMT-interested readers: the
combinatorial bookkeeping is now separated from the GMT content,
making the latter the focus where it should be. For formalization:
a recurring argument is factored out once rather than repeated in
each mechanization.

Eight structural findings the formalization surfaced are catalogued
in the paper (§4). They are not errors in the cited papers; they are
observations about places where prose compresses structure the Lean
proof cannot avoid.

## How to consume

```
require CombArg from git
  "https://github.com/MathNetwork/comb_arg.git" @ "v0.1.0"
```

Then, with `f`, `hf`, `m0`, `hm_pos`, `hm`, `N`, `hN`, and a
`witness` hypothesis in scope:

```
exact CombArg.exists_sup_reduction hf hm_pos hm hN witness
```

Details in the accompanying paper §5 and in
`examples/MinimalUsage.lean` in the repository.

## Known limitations (v0.1)

- Parameter space specialized to `unitInterval`; multi-parameter
  sweepouts require generalization.
- The `PairableCover` abstract cover class is carried in signatures
  but not load-bearing; a decision on its fate (retain as extension
  point, rework to load-bearing, or simplify out) is deferred to
  v0.2.
- No stock `PairableCover` instances are shipped beyond a trivial
  one on `ℝ` in `test/Smoke.lean`.

## Links

- Repository: <https://github.com/MathNetwork/comb_arg>
- Paper (this directory): `paper/paper.tex`
- CHANGELOG: `CHANGELOG.md`
- Zenodo DOI: to be assigned upon GitHub release of v0.1.0.

## Contact

Xinze Li, <lixinze@math.utoronto.ca>.
