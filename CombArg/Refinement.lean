/-
Copyright (c) 2026 Xinze Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xinze Li
-/
import CombArg.Refinement.CoverConstruction
import CombArg.Refinement.Disjointness
import CombArg.Refinement.Induction
import CombArg.Refinement.InitialCover
import CombArg.Refinement.Assembly
import CombArg.Refinement.PartialRefinement
import CombArg.Refinement.SpacedIntervals

/-!
# Step 1: Interval refinement construction — facade

Re-exports the seven submodules under `CombArg.Refinement.*`.
Downstream consumers can `import CombArg.Refinement` to access the
complete Step 1 API.

From the witness hypothesis (a `LocalWitness` at every
`1/N`-near-critical parameter), this module constructs a
`FiniteCoverWithWitnesses unitInterval f m₀ (1/N) (1/(4N))`: a finite
family of pieces covering the near-critical set with `twoFold` overlap
control and a `1/(4N)` saving floor. The construction follows DLT §3.2
Step 1 (De Lellis–Tasnady 2013,
*The existence of embedded minimal hypersurfaces*).

## Module layout

* [`Refinement.SpacedIntervals`](Refinement/SpacedIntervals.lean) —
  `openInterval` helper plus the abstract `SkippedSpacedIntervals`
  structure with its `chain_spacing`, `disjoint_of_even_gap`,
  `closure_disjoint_of_even_gap`, and `not_three_overlap` lemmas
  (pure 1D geometry, independent of witnesses).
* [`Refinement.InitialCover`](Refinement/InitialCover.lean) —
  `nearCritical`, `InitialCover` structure, `InitialCover.I`,
  `toSkippedSpacedIntervals` projection,
  `exists_closedBall_subset_of_open`.
* [`Refinement.CoverConstruction`](Refinement/CoverConstruction.lean) —
  `exists_initialCover` via a grid + Lebesgue-number construction.
* [`Refinement.PartialRefinement`](Refinement/PartialRefinement.lean) —
  `PartialRefinement` mid-induction state and the base case `step_zero`.
* [`Refinement.Induction`](Refinement/Induction.lean) —
  `ExtendResult`, `step_succ_at`, and
  `exists_terminal_refinement` (bounded iteration on
  `remaining.card`).
* [`Refinement.Disjointness`](Refinement/Disjointness.lean) — the
  `InitialCover.*` chain-spacing and parity-rescue lemmas
  (`chain_spacing`, `disjoint_of_even_gap`,
  `closure_disjoint_of_even_gap`, `not_three_overlap`).
* [`Refinement.Assembly`](Refinement/Assembly.lean) —
  `terminal_twoFold`, `saving_bound_closure`, and the top-level
  assembly `exists_refinement`.

See also [`docs/design-notes.md`](../docs/design-notes.md) for the
design rationale, especially §4 (specialization to `unitInterval`),
§9 (witness threshold `1/(4N)`), §10 (`intervalCenter` /
`witnessCenter` split), and §11 (parity rescue for TwoFold).
-/
