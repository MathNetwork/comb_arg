/-
Copyright (c) 2026 Xinze Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xinze Li
-/
import CombArg.OneDim.InitialCover

/-!
# Step 1 — PartialRefinement state + base case

* `PartialRefinement ic l` — mid-induction state carrying `l` pieces
  `J_1, …, J_l`, an index-assignment `σ : Fin l → Fin ic.n`, and the
  two invariants `J_subset` and `processed_cover`.
* `step_zero` — the induction's base case, producing
  `PartialRefinement ic 1` by setting `J 0 := ic.I ⟨0, ic.n_pos⟩`.
-/

namespace CombArg.OneDim

open CombArg

/-! ## `PartialRefinement` — mid-induction state

The DLT Step 1 induction (De Lellis–Tasnady 2013 §3.2) builds, from an
`InitialCover` producing intervals `{I_i}` satisfying spacing condition
(a), a length-`l` sequence of pieces `J_1, …, J_l` together with an
index-assignment `σ : Fin l → Fin ic.n` such that `J_k ⊆ ic.I (σ k)`.
The induction step selects the smallest-index `I_i` not yet entirely
contained in `⋃_{k ≤ l} J_k` and splits into two cases
(`I ⊆ J ∪ I_σ` vs `I \ I_σ`) to produce `J_{l+1}`.

The structure carries **two** invariants:

* `J_subset` — paper-explicit `J_k ⊆ I_{σ(k)}`.
* `processed_cover` — derived, load-bearing in Case 2:
  `I_{σ(k)} ⊆ ⋃ J_{k'}` for each `k`. -/
structure PartialRefinement
    {f : unitInterval → ℝ} {m₀ : ℝ} {N : ℕ}
    (ic : InitialCover f m₀ N) (l : ℕ) where
  /-- The `l` pieces `J_1, …, J_l` as raw subsets of `unitInterval`.
  No topological structure assumed; in Case 2 of `step_succ_at`, `J k`
  may be open-minus-open. -/
  J : Fin l → Set unitInterval
  /-- Cover-index assignment: the `k`-th piece lies inside
  `I_{σ k}` of the initial cover. -/
  σ : Fin l → Fin ic.n
  /-- **Paper-explicit invariant** (DLT §3.2 Step 1 prose):
  `J_k ⊆ I_{σ(k)}`. -/
  J_subset : ∀ k : Fin l, J k ⊆ ic.I (σ k)
  /-- **Derived termination invariant**: each processed interval
  `I_{σ(k)}` is contained in `⋃ J_{k'}`. Used explicitly in Case 2
  of `step_succ_at` to argue the step reduces the remaining set, and
  implies `σ` is injective (derivable, not maintained). -/
  processed_cover : ∀ k : Fin l, ic.I (σ k) ⊆ ⋃ k' : Fin l, J k'

/-! ## Base case `step_zero` -/

/-- **Base case**: build a length-1 `PartialRefinement` by taking
`J 0 := ic.I ⟨0, ic.n_pos⟩` and `σ 0 := ⟨0, ic.n_pos⟩`.

Paper's "setting `J_1 := I_1`". Both invariants discharge by
definitional equality: `J 0 = ic.I (σ 0)`, and `⋃ k' : Fin 1, J k'`
unfolds to `J 0` (since `Fin 1` is a singleton), so
`ic.I (σ 0) = J 0 ⊆ ⋃ k', J k'`. -/
def step_zero
    {f : unitInterval → ℝ} {m₀ : ℝ} {N : ℕ}
    (ic : InitialCover f m₀ N) : PartialRefinement ic 1 where
  J := fun _ => ic.I ⟨0, ic.n_pos⟩
  σ := fun _ => ⟨0, ic.n_pos⟩
  J_subset := fun _ => subset_refl _
  processed_cover := fun _ => by
    intro t ht
    exact Set.mem_iUnion.mpr ⟨0, ht⟩

end CombArg.OneDim
