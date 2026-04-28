/-
Copyright (c) 2026 Xinze Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xinze Li
-/
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact

/-!
# `CombArg.Common.SavingClosure` — saving-bound closure extension

A small helper packaging the recurring idiom:

  > a continuous "saving" $f - g$ that is bounded below by $c$ on an
  > open set $U$ is also bounded below by $c$ on $\overline{U}$.

The level set $\{s \mid c \le f(s) - g(s)\}$ is closed under
continuity of $f$ and $g$ (`isClosed_le`), so containment of $U$ in
that level set lifts to containment of $\overline{U}$
(`IsClosed.closure_subset_iff`).

This pattern appears in both tiers:

* `OneDim/DLTCover.lean`'s `saving_bound_closure` extends the witness
  saving from the open piece `J k` to its closure `closure (J k)`;
* `Scalar/Partition.lean`'s `chosenTk_saving_bound` extends the
  witness saving from the open `Ioo`-preimage to its closure (which
  contains the closed partition piece).

Both call sites collapse to a single application of
`sub_ge_of_closure`. The helper lives under `CombArg/Common/` rather
than under either tier so neither imports the other through it.
-/

namespace CombArg

/-- A continuous saving $f - g$ bounded below by $c$ on a set $U$ is
also bounded below by $c$ on the closure $\overline{U}$. -/
lemma sub_ge_of_closure
    {K : Type*} [TopologicalSpace K] {f g : K → ℝ} {U : Set K} {c : ℝ}
    (hf : Continuous f) (hg : Continuous g)
    (h : ∀ s ∈ U, c ≤ f s - g s)
    {t : K} (ht : t ∈ closure U) : c ≤ f t - g t :=
  (isClosed_le continuous_const (hf.sub hg)).closure_subset_iff.mpr h ht

end CombArg
