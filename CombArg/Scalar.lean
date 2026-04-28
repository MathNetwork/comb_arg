/-
Copyright (c) 2026 Xinze Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xinze Li
-/
import CombArg.Scalar.Partition

/-!
# `CombArg.Scalar` — alternative cheap proofs of the abstract scalar theorem

A `Scalar/` tier separate from the DLT-faithful `OneDim/` tier.
Both produce the same abstract output `FiniteCoverWithWitnesses
unitInterval f m₀ (1/N) (1/(4N))`, but `Scalar` proofs do not
preserve the spacing / positive-measure overlap structure that a
geometric modified-sweepout lift requires.

## Module layout

* [`Scalar.Partition`](Scalar/Partition.lean) ---
  `exists_refinement_partition`, the partition-by-endpoints proof.
  The construction is split into seven internal modules under
  `Scalar.Partition.*`:

  - `Helpers` — closure-of-preimage and open-Ioo helpers (subspace
    topology).
  - `CoverIvl` — per-witness `(a, b)` interval data and the
    Ioo-preimage open cover of `nearCritical`.
  - `Endpoints` — endpoint Finset, sorted into a strictly
    increasing list, with membership lemmas.
  - `Pieces` — partition pieces between consecutive sorted
    endpoints, with `mem_piece_iff` and index lookups for
    `(bounds tk).1` / `(bounds tk).2`.
  - `WitnessSelection` — for each piece intersecting
    `nearCritical`, pick a covering witness `tk ∈ T` such that the
    piece sits inside `val⁻¹(Icc a_tk b_tk)`.
  - `Multiplicity` — pieces have multiplicity ≤ 2 (consecutive
    pieces share only an endpoint; non-consecutive are disjoint by
    strict monotonicity of the sorted list).
  - `Coverage` — the pieces cover `unitInterval`, hence
    `nearCritical`.

  The main `Scalar/Partition.lean` then assembles these into a
  subtype-indexed `FiniteCoverWithWitnesses`, dropping pieces that
  do not intersect `nearCritical`.

The dependency graph confirms: `Scalar/Partition` does not
import `OneDim/SpacedIntervals`, `OneDim/Induction`,
`OneDim/PartialRefinement`, or `OneDim/Assembly` --- only the
shared infrastructure (`Cover`, `Witness`, `OneDim/InitialCover`
for the `nearCritical` definition). See
`paper/sections/intro.tex` Remark 1.5 for the architectural
rationale.
-/
