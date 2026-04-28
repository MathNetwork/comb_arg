/-
Copyright (c) 2026 Xinze Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xinze Li
-/
import CombArg.Scalar.Partition.CoverIvl
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Sort

/-!
# `CombArg.Scalar.Partition.Endpoints` — endpoint Finset and sorted list

From a finite subcover indexed by `T : Finset (↥(nearCritical f m₀ N))`,
collect all interval endpoints `{0, 1, (bounds tk).1, (bounds tk).2 : tk ∈ T}`
into a Finset `endpts T` of reals, sort it, and read off the partition
pieces between consecutive sorted endpoints.
-/

namespace CombArg.Scalar.Partition

open CombArg CombArg.OneDim
open scoped Classical

variable {f : unitInterval → ℝ} {m₀ : ℝ} {N : ℕ}
variable
  (witness : ∀ t : unitInterval, f t ≥ m₀ - 1 / (N : ℝ) →
                LocalWitness unitInterval f t (1 / (4 * (N : ℝ))))

/-- Endpoints of the witness intervals together with `0` and `1`. -/
noncomputable def endpts (T : Finset ↥(nearCritical f m₀ N)) :
    Finset ℝ :=
  insert (0 : ℝ) (insert (1 : ℝ)
    (T.image (fun tk => (bounds witness tk).1)
      ∪ T.image (fun tk => (bounds witness tk).2)))

/-- `endpts T` contains `0` and `1`, hence has at least two elements. -/
lemma endpts_card_ge_two (T : Finset ↥(nearCritical f m₀ N)) :
    2 ≤ (endpts witness T).card :=
  Finset.one_lt_card.mpr
    ⟨0, Finset.mem_insert_self _ _,
     1, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),
     by norm_num⟩

/-- The sorted list of endpoints, in non-decreasing order (using the
default `(· ≤ ·)` relation on `ℝ`). -/
noncomputable def sortedEndpts (T : Finset ↥(nearCritical f m₀ N)) :
    List ℝ :=
  (endpts witness T).sort

/-- The sorted endpoint list has length equal to the endpoint Finset's
cardinality. -/
lemma sortedEndpts_length (T : Finset ↥(nearCritical f m₀ N)) :
    (sortedEndpts witness T).length = (endpts witness T).card :=
  Finset.length_sort _

/-- The sorted endpoint list is strictly increasing. (`Finset.sort`
of a Finset --- which has no duplicates --- ascending is strict.) -/
lemma sortedEndpts_sortedLT (T : Finset ↥(nearCritical f m₀ N)) :
    (sortedEndpts witness T).SortedLT :=
  Finset.sortedLT_sort _

/-- The sorted endpoint list contains exactly the elements of the
endpoint Finset. -/
lemma mem_sortedEndpts_iff (T : Finset ↥(nearCritical f m₀ N))
    (x : ℝ) : x ∈ sortedEndpts witness T ↔ x ∈ endpts witness T :=
  Finset.mem_sort _

/-- Each `(bounds tk).1` is in the endpoint Finset (and hence in the
sorted list). -/
lemma bounds_left_mem_endpts {T : Finset ↥(nearCritical f m₀ N)}
    {tk : ↥(nearCritical f m₀ N)} (htk : tk ∈ T) :
    (bounds witness tk).1 ∈ endpts witness T := by
  unfold endpts
  refine Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ?_)
  exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨tk, htk, rfl⟩)

/-- Each `(bounds tk).2` is in the endpoint Finset. -/
lemma bounds_right_mem_endpts {T : Finset ↥(nearCritical f m₀ N)}
    {tk : ↥(nearCritical f m₀ N)} (htk : tk ∈ T) :
    (bounds witness tk).2 ∈ endpts witness T := by
  unfold endpts
  refine Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ?_)
  exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨tk, htk, rfl⟩)

end CombArg.Scalar.Partition
