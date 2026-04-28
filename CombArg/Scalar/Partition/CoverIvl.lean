/-
Copyright (c) 2026 Xinze Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xinze Li
-/
import CombArg.Witness
import CombArg.Common.NearCritical
import CombArg.Scalar.Partition.Helpers

/-!
# `CombArg.Scalar.Partition.CoverIvl` — per-witness interval data

For each near-critical `tk`, the witness gives an open neighborhood;
inside it we extract an open interval `Ioo (boundsLeft tk) (boundsRight tk)`
containing `tk.val.val` whose preimage under `Subtype.val` lies in the
neighborhood. The `Classical.choose` extraction is wrapped into
`noncomputable def`s with the key spec exposed as lemmas, to keep
the main proof's binder structure tractable.
-/

namespace CombArg.Scalar.Partition

open CombArg CombArg.OneDim
open scoped Classical

variable {f : unitInterval → ℝ} {m₀ : ℝ} {N : ℕ}
variable
  (witness : ∀ t : unitInterval, f t ≥ m₀ - 1 / (N : ℝ) →
                LocalWitness unitInterval f t (1 / (4 * (N : ℝ))))

/-- The bundled `(a, b)` extracted from the open neighborhood of the
witness at a near-critical point `tk`. -/
noncomputable def bounds (tk : ↥(nearCritical f m₀ N)) : ℝ × ℝ :=
  let h := exists_open_Ioo_subset_of_open
            (witness tk.val tk.property).isOpen_neighborhood
            (witness tk.val tk.property).t_mem
  ⟨h.choose, h.choose_spec.choose⟩

/-- Defining property of `bounds`: `tk.val.val` lies strictly inside
the interval, and the preimage of the open interval is contained in
the witness neighborhood. -/
lemma bounds_spec (tk : ↥(nearCritical f m₀ N)) :
    (bounds witness tk).1 < tk.val.val ∧ tk.val.val < (bounds witness tk).2 ∧
    Subtype.val ⁻¹' Set.Ioo (bounds witness tk).1 (bounds witness tk).2
      ⊆ (witness tk.val tk.property).neighborhood :=
  let h := exists_open_Ioo_subset_of_open
            (witness tk.val tk.property).isOpen_neighborhood
            (witness tk.val tk.property).t_mem
  h.choose_spec.choose_spec

/-- The `Ioo`-preimage open cover at a near-critical point. -/
noncomputable def coverIvl (tk : ↥(nearCritical f m₀ N)) :
    Set unitInterval :=
  Subtype.val ⁻¹' Set.Ioo (bounds witness tk).1 (bounds witness tk).2

/-- `coverIvl` is open. -/
lemma isOpen_coverIvl (tk : ↥(nearCritical f m₀ N)) :
    IsOpen (coverIvl witness tk) :=
  isOpen_Ioo.preimage continuous_subtype_val

/-- Each near-critical point lies in its own `coverIvl`. -/
lemma mem_coverIvl_self (tk : ↥(nearCritical f m₀ N)) :
    tk.val ∈ coverIvl witness tk := by
  show tk.val.val ∈ Set.Ioo (bounds witness tk).1 (bounds witness tk).2
  have h := bounds_spec witness tk
  exact ⟨h.1, h.2.1⟩

/-- The family `{coverIvl tk}` covers `nearCritical`. -/
lemma coverIvl_covers_nearCritical :
    nearCritical f m₀ N ⊆ ⋃ tk : ↥(nearCritical f m₀ N), coverIvl witness tk := by
  intro t ht
  exact Set.mem_iUnion.mpr ⟨⟨t, ht⟩, mem_coverIvl_self witness ⟨t, ht⟩⟩

end CombArg.Scalar.Partition
