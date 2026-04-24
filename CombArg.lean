-- Combinatorial main theorem: 1D cover refinement.
import CombArg.Refinement

-- Sup-reduction bookkeeping corollary (generic `K`).
import CombArg.Core

-- One-parameter specialization composing the two.
import CombArg.SupReduction

-- Shared infrastructure (input structures, utilities).
import CombArg.Witness
import CombArg.EnergyBound
import CombArg.Util

/-!
# `CombArg` — top-level facade

Re-exports the library modules. The declarations promoted as the
library's stable public API are:

* `CombArg.Refinement.exists_refinement` — **combinatorial main
  theorem**: from a family of `LocalWitness` data on the
  near-critical set of `f : unitInterval → ℝ`, constructs a
  `FiniteCoverWithWitnesses` with two-fold overlap and uniform
  per-piece saving `1/(4N)`. This is the non-trivial content
  extracted from the Almgren--Pitts combinatorial argument
  (Lebesgue-number cover, bounded smallest-index refinement,
  parity-rescue two-fold invariant).

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
