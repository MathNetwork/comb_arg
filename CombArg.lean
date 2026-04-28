-- Combinatorial main theorem: 1D cover refinement (DLT-faithful path).
import CombArg.OneDim

-- Alternative cheap proof of the abstract scalar theorem.
import CombArg.Scalar

-- Sup-reduction bookkeeping corollary (generic `K`).
import CombArg.Cover

-- One-parameter specialization composing the two.
import CombArg.SupReduction

-- Shared infrastructure (input structures, utilities).
import CombArg.Witness

/-!
# `CombArg` — top-level facade

Re-exports the library modules. The declarations promoted as the
library's stable public API are:

* `CombArg.OneDim.exists_DLTCover` — **structured DLT-style cover**:
  the Stage A + B output exposing initial-cover spacing, partial
  refinement, σ-injectivity, and the termination invariant. Consumed
  by future geometric modified-sweepout lifts that require
  positive-measure overlap on `J_i ∩ J_{i+1}`.

* `CombArg.OneDim.exists_refinement` — **combinatorial main
  theorem (DLT path)**: the abstract scalar output, defined as
  `(exists_DLTCover ...).toFinite`. From a family of `LocalWitness`
  data on the near-critical set of `f : unitInterval → ℝ`,
  constructs a `FiniteCoverWithWitnesses` with two-fold overlap and
  uniform per-piece saving `1/(4N)`.

* `CombArg.Scalar.exists_refinement_partition` — **alternative
  scalar proof**: the same conclusion via a partition-by-endpoints
  argument. Strictly cheaper than the DLT path, but discards the
  overlap structure and is therefore unsuitable as input for a
  geometric lift. See `paper/sections/intro.tex` Remark 1.5 for the
  design rationale.

* `CombArg.exists_sup_reduction_of_cover` — **sup-reduction
  bookkeeping corollary** (generic `K`): from any
  `FiniteCoverWithWitnesses` on a compact nonempty space `K`,
  produces a competitor `f'` with
  `sSup (range f') ≤ m₀ − ε`. Three-line arithmetic over the
  cover data.

* `CombArg.exists_sup_reduction` — **one-parameter
  specialization** on `unitInterval` with
  `(δ, ε) = (1/N, 1/(4N))`. Composition of the two above.
-/
