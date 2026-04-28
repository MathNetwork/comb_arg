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

Files:

* [`Scalar.Partition`](Scalar/Partition.lean) ---
  `exists_refinement_partition`. Partition-by-endpoints proof:
  compactness of the near-critical set yields a finite open
  subcover; sorting the witness-interval endpoints partitions the
  unit interval into closed pieces of multiplicity `≤ 2`; for each
  non-empty piece a covering witness is selected and the saving
  bound is extended from the open `Ioo` interior to the closed
  piece by continuity.

The dependency graph confirms: `Scalar/Partition.lean` does not
import `OneDim/SpacedIntervals`, `OneDim/Induction`,
`OneDim/PartialRefinement`, or `OneDim/Assembly` --- only the
shared infrastructure (`Cover`, `Witness`, `OneDim/InitialCover`
for the `nearCritical` definition). See
`paper/sections/intro.tex` Remark 1.5 for the architectural
rationale.
-/
