/-
Copyright (c) 2026 Xinze Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xinze Li
-/
import Mathlib.Topology.MetricSpace.Defs

/-!
# `LocalWitness` — local replacement data at a near-critical parameter

`LocalWitness K f t ε` bundles the data attached to a parameter `t : K`
where the energy `f : K → ℝ` is near its supremum:

* an open neighborhood of `t` in `K`,
* a continuous replacement-energy function `replacementEnergy : K → ℝ`,
* a uniform saving of at least `ε` on the neighborhood:
  `f s − replacementEnergy s ≥ ε` for every `s` in the neighborhood.

The replacement is represented *only by its energy*, not by a concrete
family `K → X` in some ambient space — keeping the combinatorial
theorem agnostic to how the replacement is realized in any ambient
geometry. See `docs/design-notes.md` §5 for the rationale.

The saving threshold `ε : ℝ` is an abstract parameter with no
built-in numerical constant. Concrete relationships to a
near-criticality level `N` (e.g. `ε = 1/(4N)`) enter at use sites
(`SupReduction.lean`, `Refinement/`), not here.
-/

namespace CombArg

/-- **Local witness at a near-critical parameter.**

At a parameter `t : K`, a `LocalWitness K f t ε` supplies an open
neighborhood of `t`, a continuous replacement-energy function on `K`,
and a quantitative saving of at least `ε` on the neighborhood. -/
structure LocalWitness
    (K : Type*) [TopologicalSpace K]
    (f : K → ℝ) (t : K) (ε : ℝ) where
  /-- An open neighborhood of `t` on which the saving holds. -/
  neighborhood : Set K
  /-- The neighborhood is open. -/
  isOpen_neighborhood : IsOpen neighborhood
  /-- The base parameter lies in the neighborhood. -/
  t_mem : t ∈ neighborhood
  /-- Energy of the replacement at each parameter in `K`. (Behavior
  outside `neighborhood` is unconstrained beyond continuity.) -/
  replacementEnergy : K → ℝ
  /-- The replacement energy is continuous. Required so the saving
  bound extends from the open `neighborhood` to its closure: the
  refinement induction in `Refinement/` takes closed pieces (closures
  of open `Set.Ioo` pieces) and needs the witness bound to hold on
  boundary points. -/
  replacementEnergy_continuous : Continuous replacementEnergy
  /-- **Quantitative saving.** On the neighborhood, the replacement
  undercuts `f` by at least `ε`. -/
  saving_bound :
    ∀ s ∈ neighborhood,
      f s - replacementEnergy s ≥ ε

end CombArg
