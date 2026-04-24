/-
Copyright (c) 2026 Xinze Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xinze Li
-/
import CombLemma

/-!
# Smoke test

A trivial `PairableCover` instance that type-checks, confirming the
definitions in `Witness.lean` are consistent.
-/

namespace CombLemma.Test

/-- Trivial `PairableCover` structure on `ℝ` with a single empty cover.
Used only to exercise the definitions; carries no mathematical content. -/
noncomputable instance : PairableCover ℝ where
  Cover := Unit
  leftRegion _ := ∅
  rightRegion _ := ∅
  diameter _ := 0
  diameter_nonneg _ := le_refl 0
  regions_disjoint _ := by simp
  diameter_nesting _ _ _ hne := by simp at hne

end CombLemma.Test
