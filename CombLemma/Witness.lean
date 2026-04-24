/-
Copyright (c) 2026 Xinze Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xinze Li
-/
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.MetricSpace.Basic

/-!
# Basic definitions

Abstract objects underlying the min-max combinatorial selection argument.

See `docs/design-notes.md` for the design rationale.

* `PairableCover X` is a typeclass over a pseudo-metric space `X`. It
  exposes an abstract type `Cover` of paired covers, two region-extraction
  projections, a scalar diameter, and a small number of axioms tailored to
  the diameter-based induction of Step 1 (see `Refinement.lean`).

* `LocalWitness` bundles the data attached to a near-critical parameter
  `t : K`: an open neighborhood, a cover, a replacement-energy function,
  and a quantitative saving by at least a threshold `ε`. The replacement
  is represented *only by its energy*, not by a concrete family `K → X`,
  so that GMT content stays outside this repo. The saving threshold is
  left as an abstract parameter `ε : ℝ`; concrete relationships to
  a near-criticality level (e.g. `ε = 1/(4N)`) enter at use sites
  (`SupReduction.lean`, `EnergyBound.lean`).
-/

namespace CombLemma

/-- **Abstract pairable-cover class.**

An instance of `PairableCover X` encodes a family of "paired" subsets of
`X`: each cover `c : Cover` determines a left region, a right region, and
a scalar diameter controlling its scale. The axioms below correspond to
conditions anticipated for the diameter-based induction in Step 1.

See `docs/design-notes.md` for the design rationale. -/
class PairableCover (X : Type*) [PseudoMetricSpace X] where
  /-- Abstract type of covers. -/
  Cover : Type*
  /-- Left region of a cover. -/
  leftRegion : Cover → Set X
  /-- Right region of a cover. -/
  rightRegion : Cover → Set X
  /-- Scalar diameter of a cover. -/
  diameter : Cover → ℝ
  /-- Diameter is non-negative. -/
  diameter_nonneg : ∀ c : Cover, 0 ≤ diameter c
  /-- Left and right regions are disjoint. -/
  regions_disjoint : ∀ c : Cover, Disjoint (leftRegion c) (rightRegion c)
  /-- **Diameter-nesting axiom.**

  If two covers have overlapping combined regions (left ∪ right), and
  `c₁` has diameter ≤ `c₂`'s, then `c₁`'s combined region is contained
  in `c₂`'s. Nesting ⇒ either equal combined regions or strict diameter
  inequality (otherwise mutual inclusion would force equality on both
  sides).

  Anticipated as the interface ordering overlapping covers in a
  diameter-based interval refinement induction. See
  `docs/design-notes.md §8`. -/
  diameter_nesting :
    ∀ c₁ c₂ : Cover, diameter c₁ ≤ diameter c₂ →
      ((leftRegion c₁ ∪ rightRegion c₁) ∩
        (leftRegion c₂ ∪ rightRegion c₂)).Nonempty →
      (leftRegion c₁ ∪ rightRegion c₁) ⊆
        (leftRegion c₂ ∪ rightRegion c₂)

/-- The combined region of a cover: the union of its left and right
regions. A convenience abbreviation; downstream lemmas read more cleanly
than repeating `leftRegion c ∪ rightRegion c`. -/
def PairableCover.combinedRegion {X : Type*} [PseudoMetricSpace X]
    [PairableCover X] (c : PairableCover.Cover X) : Set X :=
  PairableCover.leftRegion c ∪ PairableCover.rightRegion c

/-- `diameter_nesting` restated in terms of `combinedRegion`. Unfolds
definitionally to the class axiom; provided here so downstream code can
prefer the tidier form. -/
lemma PairableCover.diameter_nesting_combined
    {X : Type*} [PseudoMetricSpace X] [PairableCover X]
    (c₁ c₂ : PairableCover.Cover X)
    (h : PairableCover.diameter c₁ ≤ PairableCover.diameter c₂)
    (hne : (PairableCover.combinedRegion c₁ ∩
             PairableCover.combinedRegion c₂).Nonempty) :
    PairableCover.combinedRegion c₁ ⊆ PairableCover.combinedRegion c₂ :=
  PairableCover.diameter_nesting c₁ c₂ h hne

/-- **Local witness at a near-critical parameter.**

At a parameter `t : K`, a `LocalWitness K X f t ε` supplies:

* an open neighborhood of `t` in `K`,
* a cover `c : PairableCover.Cover`,
* a replacement-energy function `replacementEnergy : K → ℝ`,
* a uniform saving of at least `ε` on the neighborhood.

The replacement is represented *only* by its energy (not by a concrete
family `K → X`), keeping the combinatorial theorem agnostic to how the
replacement is realized in the ambient space.

The saving threshold `ε : ℝ` is an abstract parameter with no built-in
numerical constant; concrete relationships to a near-criticality level
`N` (e.g. `ε = 1/(4N)`, `ε ≥ m₀ - f t`) enter *at use sites* such as
`SupReduction.lean` or `EnergyBound.lean`, not here. -/
structure LocalWitness
    (K : Type*) [TopologicalSpace K]
    (X : Type*) [PseudoMetricSpace X] [PairableCover X]
    (f : K → ℝ) (t : K) (ε : ℝ) where
  /-- An open neighborhood of `t` on which the saving holds. -/
  neighborhood : Set K
  /-- The neighborhood is open. -/
  isOpen_neighborhood : IsOpen neighborhood
  /-- The base parameter lies in the neighborhood. -/
  t_mem : t ∈ neighborhood
  /-- The paired cover witnessing the local replacement. -/
  cover : PairableCover.Cover (X := X)
  /-- Energy of the replacement at each parameter in `K`. (Behavior outside
  `neighborhood` is unconstrained.) -/
  replacementEnergy : K → ℝ
  /-- The replacement energy is continuous. Required so the saving bound
  extends from the open `neighborhood` to its closure: the refinement
  induction in `Refinement.lean` takes closed pieces (closures of open
  `Set.Ioo` pieces) and needs the witness bound to hold on boundary
  points. Standard for GMT-sourced witnesses. -/
  replacementEnergy_continuous : Continuous replacementEnergy
  /-- **Quantitative saving.** On the neighborhood, the replacement undercuts
  `f` by at least `ε`. -/
  saving_bound :
    ∀ s ∈ neighborhood,
      f s - replacementEnergy s ≥ ε

end CombLemma
