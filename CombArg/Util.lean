/-
Copyright (c) 2026 Xinze Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xinze Li
-/
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact

/-!
# Utility lemmas

Small reusable pieces extracted from the main developments so they
can be applied generically.

* `ge_of_closure_of_ge` — a continuous real-valued function bounded
  below on a set is bounded below on its closure. Uses the fact
  that `{s : g s ≥ c}` is closed under continuity of `g`.
* `exists_even_gap_of_three` — pure integer fact: among three
  strictly increasing naturals $a < b < c$, some pair has
  difference that is even and at least $2$.
-/

namespace CombArg

/-- If `g : X → ℝ` is continuous and `g s ≥ c` for every `s ∈ U`,
then `g t ≥ c` for every `t ∈ \overline{U}`.

The preimage `{s : c ≤ g s} = g⁻¹(Ici c)` is closed under `g`
continuous; a closed superset of `U` contains `\overline{U}`. -/
lemma ge_of_closure_of_ge {X : Type*} [TopologicalSpace X]
    {g : X → ℝ} {c : ℝ} {U : Set X}
    (hg : Continuous g) (hU : ∀ s ∈ U, c ≤ g s)
    {t : X} (ht : t ∈ closure U) : c ≤ g t := by
  have hClosed : IsClosed {s : X | c ≤ g s} :=
    isClosed_le continuous_const hg
  exact hClosed.closure_subset_iff.mpr hU ht

/-- Pure integer fact: among any three strictly increasing
naturals $a < b < c$, some pair has difference that is even and
at least $2$. Used in the parity-rescue argument on
`InitialCover` indices. -/
lemma exists_even_gap_of_three {a b c : ℕ} (hab : a < b) (hbc : b < c) :
    (2 ≤ c - a ∧ (c - a) % 2 = 0) ∨
    (2 ≤ b - a ∧ (b - a) % 2 = 0) ∨
    (2 ≤ c - b ∧ (c - b) % 2 = 0) := by
  omega

end CombArg
