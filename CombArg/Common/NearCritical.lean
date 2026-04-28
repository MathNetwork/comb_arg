/-
Copyright (c) 2026 Xinze Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xinze Li
-/
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.Compact

/-!
# `CombArg.Common.NearCritical` — the near-critical set

The `1/N`-near-critical set `nearCritical f m₀ N := {t : K | f t ≥ m₀ - 1/N}`
together with its closedness, compactness, and non-emptiness
properties.

This definition is shared by both tiers of `CombArg`:

* the DLT-faithful `CombArg.OneDim` path consumes it through
  `OneDim.InitialCover` (the `Set` whose Lebesgue-number cover by
  witness neighborhoods becomes the initial cover);
* the cheap `CombArg.Scalar.Partition` path consumes it directly
  (compactness gives a finite open subcover by witness `Ioo`-preimages).

Keeping `nearCritical` in `CombArg/Common/` rather than under
`CombArg/OneDim/` lets the `Scalar/Partition` tier import this file
without pulling any `OneDim/*` dependency, making the two-tier
dependency-graph separation behind paper Remark 1.5 strictly
verifiable: `lake build CombArg.Scalar.Partition` does not compile
any `OneDim/*` source.

The namespace is kept as `CombArg.OneDim` for v0.4 API stability:
`CombArg.OneDim.nearCritical` is the stable public name listed in
README.
-/

namespace CombArg.OneDim

variable {K : Type*} [TopologicalSpace K]
    {f : K → ℝ} {m₀ : ℝ} {N : ℕ}

/-- The `1/N`-near-critical set of `f` with respect to `m₀`. -/
def nearCritical (f : K → ℝ) (m₀ : ℝ) (N : ℕ) : Set K :=
  {t : K | f t ≥ m₀ - 1 / (N : ℝ)}

omit [TopologicalSpace K] in
/-- Membership in `nearCritical` unfolds to the defining inequality
`f t ≥ m₀ - 1/N`. Holds without a topological structure on `K`. -/
@[simp] lemma mem_nearCritical {t : K} :
    t ∈ nearCritical f m₀ N ↔ f t ≥ m₀ - 1 / (N : ℝ) := Iff.rfl

/-- The near-critical set is closed: it is the preimage of the closed
half-line `[m₀ - 1/N, ∞)` under continuous `f`. -/
lemma isClosed_nearCritical (hf : Continuous f) :
    IsClosed (nearCritical f m₀ N) :=
  isClosed_le continuous_const hf

/-- The near-critical set is compact: closed subset of compact `K`. -/
lemma isCompact_nearCritical [CompactSpace K] (hf : Continuous f) :
    IsCompact (nearCritical f m₀ N) :=
  (isClosed_nearCritical hf).isCompact

/-- The near-critical set is nonempty: a maximizer of `f` on `K` attains
`m₀ = sSup (range f)` and hence satisfies `f t₀ ≥ m₀ - 1/N`. -/
lemma nearCritical_nonempty [CompactSpace K] [Nonempty K]
    (hf : Continuous f) (hm : m₀ = sSup (Set.range f)) (hN : 0 < N) :
    (nearCritical f m₀ N).Nonempty := by
  obtain ⟨t₀, _, ht₀⟩ :=
    isCompact_univ.exists_isMaxOn Set.univ_nonempty hf.continuousOn
  refine ⟨t₀, ?_⟩
  show f t₀ ≥ m₀ - 1 / (N : ℝ)
  have hle : m₀ ≤ f t₀ := by
    rw [hm]
    refine csSup_le ⟨f t₀, Set.mem_range_self _⟩ ?_
    rintro x ⟨t, rfl⟩
    exact ht₀ (Set.mem_univ t)
  have hinv : (0 : ℝ) < 1 / (N : ℝ) :=
    one_div_pos.mpr (Nat.cast_pos.mpr hN)
  linarith

end CombArg.OneDim
