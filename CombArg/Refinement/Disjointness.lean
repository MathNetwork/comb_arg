/-
Copyright (c) 2026 Xinze Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xinze Li
-/
import CombArg.Refinement.InitialCover
import CombArg.Refinement.SpacedIntervals

/-!
# Step 1 — Disjointness, thin wrappers over `SkippedSpacedIntervals`

The geometric content of spacing condition (a) lives on the
ambient `SkippedSpacedIntervals` structure; here we expose the
same lemmas on `InitialCover` by delegating to the projection
`InitialCover.toSkippedSpacedIntervals`.

* `InitialCover.chain_spacing` — iterated spacing (a) at gap `2(m+1)`.
* `InitialCover.disjoint_of_even_gap` — open-interval disjointness.
* `InitialCover.closure_disjoint_of_even_gap` — closed-interval
  disjointness.
* `InitialCover.not_three_overlap` — parity rescue: no point
  lies in three `closure (ic.I _)` at distinct sorted indices.

All proofs are one-line applications of the abstract lemmas on
`SkippedSpacedIntervals` (see `Refinement/SpacedIntervals.lean`).
-/

namespace CombArg.Refinement

namespace InitialCover

variable {f : unitInterval → ℝ} {m₀ : ℝ} {N : ℕ}

/-- **Chain spacing**, delegated from
`SkippedSpacedIntervals.chain_spacing`. -/
lemma chain_spacing
    (ic : InitialCover f m₀ N) (i : Fin ic.n) :
    ∀ (m : ℕ) (j : Fin ic.n), j.val = i.val + 2 * (m + 1) →
      (ic.intervalCenter i).val + ic.radius i <
        (ic.intervalCenter j).val - ic.radius j :=
  ic.toSkippedSpacedIntervals.chain_spacing i

/-- **Even-gap disjointness**, delegated from
`SkippedSpacedIntervals.disjoint_of_even_gap`. -/
lemma disjoint_of_even_gap
    (ic : InitialCover f m₀ N) (i j : Fin ic.n)
    (m : ℕ) (h_gap : j.val = i.val + 2 * (m + 1)) :
    Disjoint (ic.I i) (ic.I j) := by
  simpa only [ic.toSkippedSpacedIntervals_I] using
    ic.toSkippedSpacedIntervals.disjoint_of_even_gap i j m h_gap

/-- **Closed-interval disjointness**, delegated from
`SkippedSpacedIntervals.closure_disjoint_of_even_gap`. -/
lemma closure_disjoint_of_even_gap
    (ic : InitialCover f m₀ N) (i j : Fin ic.n)
    (m : ℕ) (h_gap : j.val = i.val + 2 * (m + 1)) :
    Disjoint (closure (ic.I i)) (closure (ic.I j)) := by
  simpa only [ic.toSkippedSpacedIntervals_I] using
    ic.toSkippedSpacedIntervals.closure_disjoint_of_even_gap i j m h_gap

/-- **Parity rescue**, delegated from
`SkippedSpacedIntervals.not_three_overlap`. -/
lemma not_three_overlap
    (ic : InitialCover f m₀ N)
    (a b c : Fin ic.n) (hab : a.val < b.val) (hbc : b.val < c.val)
    (t : unitInterval)
    (ha : t ∈ closure (ic.I a)) (hb : t ∈ closure (ic.I b))
    (hc : t ∈ closure (ic.I c)) :
    False := by
  have ha' : t ∈ closure (ic.toSkippedSpacedIntervals.I a) := by
    rwa [ic.toSkippedSpacedIntervals_I]
  have hb' : t ∈ closure (ic.toSkippedSpacedIntervals.I b) := by
    rwa [ic.toSkippedSpacedIntervals_I]
  have hc' : t ∈ closure (ic.toSkippedSpacedIntervals.I c) := by
    rwa [ic.toSkippedSpacedIntervals_I]
  exact ic.toSkippedSpacedIntervals.not_three_overlap a b c hab hbc t
    ha' hb' hc'

end InitialCover

end CombArg.Refinement
