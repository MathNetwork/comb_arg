/-
Copyright (c) 2026 Xinze Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xinze Li
-/
import CombArg

/-!
# Minimal-usage pattern for `CombArg.exists_sup_reduction`

This file sketches the invocation pattern for the library's main
theorem from a downstream consumer's perspective. It is deliberately
an **outline** rather than a runnable end-to-end example: constructing
a concrete `LocalWitness` with a GMT-style replacement family is out
of scope for the combinatorial core (see the "Scope" section of the
README), so a meaningful worked example would need either a heavy
GMT instantiation or a contrived trivial one that does not illustrate
the intended use.

## What a consumer supplies

A consumer of `exists_sup_reduction` must provide, in order:

* An **ambient space** `X : Type*` with `[PseudoMetricSpace X]` and
  `[PairableCover X]`. The `PairableCover` class exposes an abstract
  `Cover` type, two region projections, a `diameter` scalar, and the
  `diameter_nesting` axiom. The paired-cover interface is not
  load-bearing in v0.1; a trivial instance suffices for clients that
  do not need it (see `test/Smoke.lean` for a trivial instance on
  `ℝ`).

* A **continuous energy** `f : unitInterval → ℝ` with
  `hf : Continuous f`, and a scalar `m₀ : ℝ` satisfying
  `hm_pos : 0 < m₀` and `hm : m₀ = sSup (Set.range f)`.

* A **near-criticality parameter** `N : ℕ` with `hN : 0 < N`. The
  conclusion's quantitative bound is `1/(4N)`.

* A **witness hypothesis**: at every `t : unitInterval` with
  `f t ≥ m₀ - 1/N`, a `Nonempty (LocalWitness unitInterval X f t
  (1 / (4 * (N : ℝ))))`. A `LocalWitness` bundles an open
  neighborhood of `t`, a continuous `replacementEnergy : unitInterval
  → ℝ`, and the saving bound `f s - replacementEnergy s ≥ 1/(4N)` on
  the neighborhood.

  In a GMT instantiation, this witness comes from De Lellis–Tasnady
  2013's Lemma 3.1 (existence of a replacement family), Pitts 1981's
  analogue, or equivalent. Producing it is the substantive
  non-combinatorial work.

## Invocation skeleton

```lean
section
  variable {X : Type*} [PseudoMetricSpace X] [PairableCover X]
  variable (f : unitInterval → ℝ) (hf : Continuous f)
  variable {m₀ : ℝ} (hm_pos : 0 < m₀) (hm : m₀ = sSup (Set.range f))
  variable {N : ℕ} (hN : 0 < N)
  variable (witness : ∀ t : unitInterval, f t ≥ m₀ - 1 / (N : ℝ) →
      Nonempty (CombArg.LocalWitness unitInterval X f t
                  (1 / (4 * (N : ℝ)))))

  -- Conclusion: a competitor `f'` together with a modification
  -- set `S ⊆ unitInterval` exist with: (coverage) `S` contains
  -- the `1/N`-near-critical set; (a) `f' ≤ f` pointwise; (b)
  -- `f' = f` off `S`; (c) `sSup (range f') ≤ m₀ - 1/(4N)`.
  example : ∃ (f' : unitInterval → ℝ) (S : Set unitInterval),
      {t : unitInterval | f t ≥ m₀ - 1 / (N : ℝ)} ⊆ S ∧
      (∀ t, f' t ≤ f t) ∧
      (∀ t, t ∉ S → f' t = f t) ∧
      sSup (Set.range f') ≤ m₀ - 1 / (4 * (N : ℝ)) :=
    CombArg.exists_sup_reduction hf hm_pos hm hN witness
end
```

The consumer then threads `f'` into whatever downstream argument
requires a strictly-better competitor (for example, a min-max
contradiction: if `m₀` were the infimum of `sSup (range ·)` over
some admissible class `𝒜` and `f ∈ 𝒜`, showing `f' ∈ 𝒜` would
contradict the minimality of `m₀`). Conditions (a) and (b) anchor
`f'` to `f`: `f' = f` everywhere off `S`, so membership in
admissible classes that require pointwise bounds or off-support
coincidence with `f` transfers cleanly.

## What this file does not do

* It does not instantiate `PairableCover` non-trivially.
* It does not construct `LocalWitness` values.
* It does not call `exists_sup_reduction` in a way that would
  produce a specific `f'` to inspect.

For a trivial `PairableCover` instance that type-checks against
the library's definitions, see `test/Smoke.lean`.
-/
