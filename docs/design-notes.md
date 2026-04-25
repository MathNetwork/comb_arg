# Design notes

Tentative decisions made during Phase 0. All are flagged for Moqian's
review — none are final until acknowledged.

## Decisions resolved at Phase 2 prep review (2026-04-22)

Three items below are now settled; the original entries (§§1, 2, 4, 8)
remain for historical context. See the commit *"Phase 2 prep: reduction-
form main theorem, K=unitInterval in Refinement, diameter_nesting
axiom"* for the code change.

* **§1/§8 — axiom list.** `diameter_separation` (weak) replaced by
  `diameter_nesting`: if two covers have overlapping combined regions
  and `diameter c₁ ≤ diameter c₂`, then the smaller cover's combined
  region is contained in the larger's. A `combinedRegion` abbreviation
  is also added to `Witness.lean` for readable downstream proofs. This
  is the nested form anticipated in §8.
* **§2 — theorem form.** The top-level theorem is renamed
  `exists_sup_reduction` and restated as
  `∃ f' : K → ℝ, sSup (range f') < m₀` (reduction), **not**
  `... → False` (contradiction). Rationale: the contradiction form
  requires an admissible-class / min-max-level hypothesis that would
  import GMT structure contrary to the project's scope principle. See
  §2 below for the full analysis.
* **§4 — type of `K`.** Remains abstract at the `Witness.lean`,
  `EnergyBound.lean`, and `SupReduction.lean` level. `Refinement.lean`'s
  forthcoming constructor specializes to `K = unitInterval`; abstract-
  `K` generalization is Phase 3 work.

## 1. Axiom list for `PairableCover`

**Tentative choice.** The class has five fields of data and three axioms:

Data:
- `Cover : Type*` — abstract type of covers.
- `leftRegion : Cover → Set X`
- `rightRegion : Cover → Set X`
- `diameter : Cover → ℝ`

Axioms:
- `diameter_nonneg`: diameter is `≥ 0`.
- `regions_disjoint`: left and right regions are disjoint.
- `diameter_separation`: if two covers have overlapping combined
  regions, they coincide or differ in diameter.

**Rationale.** The SPEC instructs "derive the axiom list by reading what
Step 1 actually needs". Since Step 1 is not formalized yet, the above
is the **minimal** set that lets `Witness.lean` compile and that plausibly
supports a diameter-based induction. It is almost certainly incomplete
— Phase 2 will very likely need to add axioms (e.g., subcover
existence, nested diameter properties).

**Open question for Moqian.** Is the diameter-separation axiom stated
strongly enough? Alternatives considered:

1. *Current (weak):* overlapping ⇒ (equal ∨ unequal diameters).
2. *Stronger:* overlapping ⇒ (equal ∨ strictly nested regions ordered
   by diameter).
3. *Decoupled:* two separate axioms — one about overlap, one about
   diameter rank.

Option 1 leaves the most room to negotiate in Phase 2; option 2 bakes
in the induction more eagerly. Currently going with option 1.

## 2. Contradiction vs. constructive form of the main theorem

**Tentative choice.** Contradiction form: `... → False`.

**Rationale.** The natural form of the argument in the literature is:
"if the witness assumption held uniformly, we would modify the sweepout
to undercut `m₀`, contradicting the definition of `m₀`." This is
cleaner than producing a selected slice, because:

- The slice one produces in a constructive form is *the result of the
  contradiction*, not an intermediate object — it would be the
  near-critical parameter whose existence falsifies the uniform witness
  hypothesis.
- Contradiction form matches the user's original prompt and keeps the
  theorem's logical shape simple.

**Open question.** Is there a downstream consumer of this theorem that
would prefer a constructive slice? If so, the post-Phase-2 version
should expose *both*: the core `False`-conclusion result plus a
derivative `∃`-result for consumers.

## 3. Naming: `PairableCover`

**Tentative choice.** Keep `PairableCover` (per SPEC).

**Alternatives considered.** `SeparatedPairClass`, `DiameterSeparatedCover`,
`PairedCover`.

**Rationale.** `PairableCover` is the name in the SPEC and carries the
two-region intuition well. Reserve a rename for after Phase 2 if the
axiom list shifts substantially.

## 4. Type of `K`

**Tentative choice.** Abstract `Type*` with `[TopologicalSpace K]
[CompactSpace K] [Nonempty K]`.

**Rationale.** The user's original prompt used this abstract form. The
SPEC says "initially focus on `K = [0, 1]`"; deferring that
specialization keeps the theorem more general, and the one-parameter
case can be recovered by instantiating to `unitInterval` later.

**Open question for Moqian.** If Phase 1 or 2 hits an argument that
genuinely needs `K = [0,1]` (e.g., invoking the intermediate value
theorem on `f`), we should specialize. Flag early.

## 5. Shape of `LocalWitness.family`

**Tentative choice.** Do *not* expose `family : K → X`. Expose only
`replacementEnergy : K → ℝ`.

**Rationale.** The SPEC explicitly flags this as a design decision
("codomain: design decision") and stresses that GMT content should stay
outside the repo. Keeping the replacement as a scalar energy function
is maximally abstract: the combinatorial theorem need not know *how*
the replacement is realized in `X`, only its energy.

**Tradeoff.** If a Phase 3 instantiation needs to reason about the
geometric content of the replacement (not just its energy), that
instantiation will have to carry an auxiliary field. Acceptable.

**Open question for Moqian.** Does the Step 2 arithmetic ever need to
know more than the scalar energy? Suspicion: no, but verify in Phase 1.

## 6. Choice of metric-space typeclass

**Tentative choice.** `[PseudoMetricSpace X]`, not `[MetricSpace X]`.

**Rationale.** Strictly more general (no separation axiom on the
metric), and the combinatorial argument does not use `d x y = 0 → x = y`.
If a later step needs true separation, strengthen then.

## 7. Lean imports

**Tentative choice.** Narrow imports per file
(`Mathlib.Topology.MetricSpace.Basic`,
`Mathlib.Topology.Compactness.Compact`,
`Mathlib.Order.ConditionallyCompleteLattice.Basic`).

**Rationale.** Cleaner than `import Mathlib`; easier to see
dependencies. If a needed identifier is missing, the error message
points at one missing import.

## 8. Provisionality of the `PairableCover` axiom list

**Status.** The current axiom list (items #1) is explicitly **provisional**.
It is the minimal set that lets the Phase 0 skeleton compile and
plausibly supports a diameter-based induction; it has not been stress-
tested against a concrete formalization of Step 1.

**Planned re-examination.** When Phase 2 (`Refinement.lean`) begins the
interval-refinement induction in earnest, revisit the class:

- **`diameter_separation` strength.** The current weak form
  (`overlap → equal ∨ unequal diameters`) is likely too weak for a
  clean induction. Expect to strengthen toward a **nested-region**
  formulation — e.g. "overlapping covers of comparable diameter have
  their regions ordered by inclusion", or "the family of covers admits
  a diameter-rank structure compatible with region nesting".
- **Missing axioms.** Plausible candidates that have not yet been
  needed (and so are not present): existence of subcovers, covering-
  multiplicity bounds, compatibility of diameter with region measure.
- **Data vs. axiom split.** Some current data (e.g. `diameter`) may
  move to axioms over a general diameter notion, or vice versa.

**Policy.** Do not pre-emptively strengthen the class from Phase 0.
Strengthen only when a specific proof step in Phase 1 or 2 demands it,
and record the demand alongside the change.

## 9. Witness hypothesis shape: `ε = 1/(4N)`, not `∃ ε > 0`

**Decision** *(Phase 2 rework Step 4a', 2026-04-22)*. The `witness`
hypothesis in `exists_sup_reduction` (and the corresponding input
to `exists_initialCover` / `exists_refinement`) requires

```lean
Nonempty (LocalWitness K X f t (1 / (4 * (N : ℝ))))
```

— a `LocalWitness` with saving **exactly `1/(4N)`**. The earlier
`∃ ε > 0, Nonempty (LocalWitness K X f t ε)` form is abandoned.

**Why.** Step 4a's audit of the DLT arithmetic revealed the earlier
form was over-abstraction: DLT's Lemma 3.1 *does* produce a definite
`ε ≥ 1/(4N)` — not an arbitrary positive `ε`. The existential form
dropped the quantitative threshold that DLT's argument actually
maintains. Commit to `1/(4N)` in the hypothesis and the Phase 1
arithmetic's `saving_ge_quarter_N` invariant is preserved through
induction without spurious mismatch handling.

**Consequence.** `InitialCover` no longer carries `saving : ι → ℝ` and
`saving_pos : ∀ i, 0 < saving i` — the saving is uniformly `1/(4N)` by
construction, encoded in the type of `wit`. The `PartialRefinement`
induction (Step 4b) will set `saving k := 1/(4N)` constantly, making
`saving_ge` a trivial invariant to maintain.

**This is the faithful DLT formulation**: downstream users of the
theorem supply a witness matching exactly what DLT's Lemma 3.1
guarantees, not a weaker `∃ ε > 0` form.

## 10. `InitialCover`'s separation of interval center and witness center

**Decision** *(Phase 2 v2-A-i-fix, 2026-04-23)*. `InitialCover` carries
**two** maps `Fin n → unitInterval`:

* `intervalCenter : Fin n → unitInterval` — the center of `I_i`, used
  in spacing condition (a);
* `witnessCenter : Fin n → unitInterval`, with
  `witnessCenter_mem_nearCritical`, at which the `i`-th `LocalWitness` lives.

These are **linked but not identified** via
`I_subset_neighborhood : I_i ⊆ (wit i).neighborhood`.

**Why.** DLT paper §3.2 Step 1 writes `t_i ∈ K` and has a single
`t_i` serve both roles (interval center + witness center). Formalizing
this identification made the existence proof of `exists_initialCover`
intractable with the tools at hand: Lebesgue number lemma gives a
uniform radius `λ > 0` such that every `λ`-ball around a point
`t ∈ NC` fits inside **some** witness neighborhood `U_{s(t)}`, with
`s(t)` not necessarily equal to `t`. Requiring `intervalCenter i =
witnessCenter i` forces `λ-ball around s_i ⊆ (wit s_i).neighborhood`
specifically, which is not what Lebesgue provides. The radius
constraints from `I_subset_neighborhood` (per-center via each `δ_{s_i}`) and
from `covers` + `two_fold_spacing` (wanting uniform/compatible control)
cannot be satisfied simultaneously under identification.

**Paper-equivalence.** The DLT Step 1 refinement induction only uses:
(i) each `I_i`'s endpoints (via `intervalCenter i ± radius i`) for
the spacing structure; (ii) `I_i ⊆ (wit i).neighborhood` for
transporting `saving_bound` onto pieces `J_k ⊆ I_{σ k}`. The
coincidence of `intervalCenter i` and `witnessCenter i` is *paper
convenience*, not substantive to the argument. The Lean formulation
is therefore **paper-equivalent** for the downstream induction; it is
a correct abstraction-decomposition, not a drift.

See `CombArg/Refinement.lean`'s `InitialCover` docstring
and the v2-A-i-fix commit for the resolution discussion.

## Open design questions summary

| # | Question | Needs decision by |
|---|----------|-------------------|
| 1 | Is diameter-separation axiom strong enough? | Start of Phase 2 |
| 2 | Expose constructive-slice variant too? | End of Phase 1 |
| 3 | Rename `PairableCover`? | End of Phase 2 |
| 4 | Specialize `K` to `unitInterval`? | When needed |
| 5 | Expose `family : K → X` on `LocalWitness`? | End of Phase 1 |
| 6 | Strengthen to `MetricSpace`? | When needed |
| 8 | Revisit `PairableCover` axioms (esp. nested `diameter_separation`)? | Phase 2 kickoff |
| 9 | Witness hypothesis `ε = 1/(4N)` vs `∃ ε > 0`? | Phase 2 Step 4a (resolved 2026-04-22: `ε = 1/(4N)`) |
| 10 | `InitialCover`'s interval/witness center identification? | Phase 2 v2-A-ii (resolved 2026-04-23: separated) |
| 11 | `σ` non-monotonicity, even-gap-only disjointness, parity rescue for TwoFold? | Phase 2 v2-B-iv (resolved 2026-04-24: document; implementation in `Refinement.lean`) |

## 11. `σ` non-monotonicity, even-gap-only disjointness, and parity rescue

**Finding** *(Phase 2 v2-B-iv, 2026-04-24)*. DLT paper's one-sentence
claim "every point in `K` lies in at most two `J_l`'s" (Lemma 3.2)
unpacks into a three-layer structure that the formalization
surfaces.

### Layer 1: `σ` is not monotone in general

Paper's induction picks the "smallest index" at each step. The
geometric intuition — "process left to right" — suggests `σ(l) ≤
σ(l+1)` or similar monotone structure. The formalization reveals
this is not guaranteed: after a step `l+1` with Case 2's `J_{l+1}
:= I_{i_*} \ I_{σ(l)}`, the next step `l+2`'s smallest-index
choice can pick an index *less* than `σ(l+1)` if the earlier index
was skipped because `I_i ⊆ J_k ∪ I_{σ(k)}` was not checked
eagerly enough.

We do not maintain monotonicity of `σ` as a `PartialRefinement`
invariant. We do maintain `Function.Injective σ` (derivable from
`processed_cover`; maintained explicitly through iteration in
`exists_terminal_refinement`).

### Layer 2: only even-gap disjointness is provable

Spacing condition (a) constrains pairs `(i, i+2)` only. Chain
via `ic_chain_spacing` gives, for any `m ≥ 1`,

```
(intervalCenter i).val + radius i
    < (intervalCenter ⟨i.val + 2 * (m+1), _⟩).val
      − radius ⟨i.val + 2 * (m+1), _⟩
```

(same-parity indices). **This does not extend to odd-gap pairs
`(i, j)` with `j.val − i.val ≥ 3` odd**: a counter-example with
strict-monotone centers but non-uniform radii satisfies spacing
(a) on every valid `(i, i+2)` pair while yielding `ic.I i ∩
ic.I j ≠ ∅`. (Explicit numerical counter-example: `center = 0,
0.1, 0.2, 0.3`, radii chosen as outlined in the commit message for
`9868cab`.)

So `ic_disjoint_of_even_gap` (even-gap only) is the strongest
disjointness lemma provable from the current `InitialCover`
fields.

### Layer 3: parity rescue for TwoFold

Despite the even-gap restriction, Lemma 3.2 (TwoFold) is provable
via a parity argument:

> **Claim.** For any three distinct σ-indices `a < b < c` in
> `Fin ic.n`, **at least one** of the three pairs `(a, b)`,
> `(b, c)`, `(a, c)` has even gap ≥ 2.

**Proof.** `(c.val − b.val) + (b.val − a.val) = c.val − a.val`.
Case-split on parity of `c.val − a.val`:

* If `c.val − a.val` is even and ≥ 2: pair `(a, c)` works.
* If `c.val − a.val` is odd and ≥ 3: exactly one of `(c.val −
  b.val)`, `(b.val − a.val)` is even; since both are ≥ 1, the even
  one is ≥ 2.

Applying `ic_closure_disjoint_of_even_gap` (closed-interval
version of even-gap disjointness) to the identified pair gives a
contradiction with the assumption that `t` lies in all three
closures. Hence each point is in at most two `closure (pr.J k)`.

See `terminal_twoFold` and `parity_rescue_sorted` in
`CombArg/Refinement.lean`.

### Why this matters

The three-layer structure is invisible in the paper (the original
sentence "at most two J_l's" is stated as a direct consequence of
spacing (a) without unpacking). Formalization surfaces the
non-monotonicity of `σ`, the even-gap limitation of the chain, and
the parity rescue that closes the gap. This is a clean instance of
formalization producing structural observations that the original
prose-level argument compresses.

This is one of the findings logged in
[`note-draft.md`](note-draft.md) for the eventual arXiv write-up.

## §12. PairableCover scaffolding vs. load-bearing

The `reusability-audit.md` found that `PairableCover` and
`LocalWitness.cover` are carried in the type signatures but not
referenced by the proof of `exists_sup_reduction`. The combinatorial
core is effectively scalar-only (uses `LocalWitness.neighborhood`,
`t_mem`, `replacementEnergy`, `replacementEnergy_continuous`, and
`saving_bound`).

Three options were considered:

- **A (scaffolding)**: Retain `PairableCover` as extension point for
  future Phase 3 work. Document the scalar projection as a finding.
- **B (load-bearing)**: Rework the formalization to let `PairableCover`
  bite. DLT's paper uses nested pair structure `A ⊂⊂ B ⊂⊂ U'` with
  annular shell `C = B \ A`, which is substantially different from a
  left/right pair; following this faithfully would be a multi-week
  Phase 3 rebuild.
- **C (simplification)**: Remove `PairableCover` and `LocalWitness.cover`.
  Scalar-only formulation as final form; dead code eliminated.

**Decision** *(2026-04-25)*: **C** — see §14 for the v0.2 implementation.

**Date raised**: 2026-04-23. **Date resolved**: 2026-04-25.

## §13. Reframe v0.1.1: combinatorial core vs. bookkeeping corollary

**Resolved 2026-04-24.** Paper and Lean documentation framing is
reorganized so that the **main theorem** is the cover-refinement
existence (`exists_refinement`), and the scalar sup-reduction
(`exists_sup_reduction_of_cover`, `exists_sup_reduction`) is
framed as a three-line bookkeeping corollary. No Lean proofs,
signatures, or axioms change — only naming, export ordering,
docstrings, and the paper narrative.

### Why v0.1 had the framing inverted

The initial release (v0.1.0) followed the surface shape of DLT's
§3.2 — which *ends* at the supremum inequality
`sup f' ≤ m₀ − 1/(4N)` as its consumer-visible conclusion — and
promoted that sup-reduction statement to the role of "abstract
core". The cover-refinement pipeline (Lebesgue number, bounded
smallest-index induction, skip-2 parity rescue) was demoted to
"internal lemmas" feeding the core.

### Why this is the wrong way round

Under inspection, the sup-reduction theorem as stated has
near-trivial content: given a `FiniteCoverWithWitnesses`, the
competitor `f'(t) := f(t) − Σ s_l · 𝟙[t ∈ p_l]` works by a
three-line case split (Lemma `sup_le_of_saving`). The Lean proof
of `exists_sup_reduction_of_cover` does not even use
`FiniteCoverWithWitnesses.energies` — only the savings `s_l`.
The non-trivial content (Lebesgue-number cover construction,
injective-σ refinement induction, two-fold parity rescue) lives
entirely in the *production* of such a cover, which is exactly
what `exists_refinement` packages.

### What v0.1.1 changes

**Paper (`paper/paper.tex`)**:

- §1 intro Theorem 1.3 (`thm:intro-scalar`) is renamed
  "Combinatorial core" and its conclusion changed from
  "∃ f' with reduced supremum" to the cover-data (I)(II)(III)
  conditions.
- §1 intro Theorem 1.4 (`thm:intro-core`) becomes Corollary 1.4
  ("Sup reduction"), stating the competitor existence as a
  consequence of the combinatorial core.
- §2.2 `thm:core` is restated as the combinatorial core on
  `[0,1]` with `leanmargin` pointing to `exists_refinement`;
  the old `thm:core` statement (generic-`K` sup reduction)
  becomes `cor:core-sup` with `leanmargin` pointing to
  `exists_sup_reduction_of_cover`.
- §2.3 `thm:main` becomes a corollary (one-parameter
  specialization) rather than a theorem.
- §3 stages A/B/C now prove the combinatorial core directly;
  the old `lem:assembly` is removed (its content inlines as the
  closing paragraph of §3).
- Figure~1: Tier 1 is now `exists_refinement` (combinatorial
  core); Tier 2 holds both sup-reduction corollaries side by
  side; pillars P1/P2 feed Tier 1, pillar P3 feeds the generic
  corollary.

**Lean**:

- `CombArg.lean` — imports reordered (`Refinement` first) and
  expanded module docstring marking `exists_refinement` as the
  combinatorial main theorem.
- `CombArg/Refinement/Assembly.lean` — docstring on
  `exists_refinement` updated from "terminal target" to
  "combinatorial main theorem".
- `CombArg/Core.lean` — module and declaration docstrings on
  `exists_sup_reduction_of_cover` updated from "abstract core"
  to "sup-reduction bookkeeping (corollary layer)".
- `CombArg/SupReduction.lean` — docstring on
  `exists_sup_reduction` updated from "1D sup reduction"
  to "one-parameter sup-reduction corollary".

**No behavioural changes**: all proof bodies, all declaration
signatures, and the axiom audit
(`propext`, `Classical.choice`, `Quot.sound`) are unchanged.

### Why (II) "at most two pieces" is no longer redundant-looking

In the old framing, the at-most-two overlap appeared as an
*input* hypothesis to `exists_sup_reduction_of_cover`, where the
proof used it only to say "at most one extra non-negative term
in the sum" — a redundant constraint that any multiplicity would
satisfy. Reviewers reading only the corollary were right to
question its role.

In the new framing, (II) appears as a *conclusion* of the main
theorem: it is the non-trivial output of the skip-2 parity
rescue in the 1D cover construction (see §11 of this file and
`not_three_overlap_any_order`). Its role as an output of a
careful combinatorial construction — not as an unmotivated input
— is now visible from the statement.

### Scope not covered in this reframe (flagged for later)

- `README.md`: still describes `exists_sup_reduction_of_cover`
  as "Abstract core". Bring it into line with the paper framing
  when the README next gets a substantive edit (planned with
  the PairableCover §12 resolution in v0.2).
- `docs/project-overview.md`: likely needs the same treatment.
- Multi-parameter generalization `K = unitInterval^m` (still
  planned for v0.2) will introduce a second combinatorial main
  theorem alongside `exists_refinement`, not a second
  sup-reduction corollary.

## §14. v0.2 API simplification: PairableCover removal and witness shape

**Resolved 2026-04-25.** A reviewer-style audit at the v0.1.1
follow-up identified four classes of public-API issues. This
section records the resolutions; implementation lands in v0.2.

### Decisions

| Item | Decision | Rationale |
|------|----------|-----------|
| §12 (PairableCover) | **Option C — remove** | Class and `LocalWitness.cover` are scaffolding only; deleting them removes a typeclass burden the consumer cannot satisfy meaningfully. The `X` ambient-space parameter goes with it: with `Cover` gone, `LocalWitness` no longer references `X`. |
| Continuity field in `LocalWitness` | **Keep** (reconsidered) | Initial reviewer pass leaned toward moving `replacementEnergy_continuous` out as a separate predicate; on second look, every cover construction taking closures structurally needs continuity, so bundling it inside `LocalWitness` is the right shape. Splitting would add API surface (an extra hypothesis on every public theorem) for marginal cleanliness gain. |
| Witness wrapping | **Drop `Nonempty`** | Public theorems take `witness : ∀ t, … → LocalWitness …` directly. The `Nonempty` wrapper required the receiver to call `Classical.choice` for no purpose: any caller capable of producing nonemptiness can produce an explicit witness. |
| Output existential shape | **Keep `∃ f' …`** | Returning a structure (`SupReducer K f m₀ ε`) instead of an `∃` was considered. Mathlib `exists_*` convention prefers `∃`, and the existing 4-/5-tuple is destructured fluently with `obtain`. Not worth a new public structure. |
| Unused positivity hypotheses | **Drop** | `_hδ : 0 < δ`, `_hε : 0 < ε` on `exists_sup_reduction_of_cover` and `_hm_pos : 0 < m₀` on `exists_sup_reduction` are bound but never consumed in proofs. Underscored binders in the public API mislead readers and trip Mathlib's unused-arg linter. |
| `EnergyBound.lean` stub | **Delete** | The 19-line re-export stub from the v0.1 → v0.1.1 reframe (when `EnergyBound` content moved into `Core`) is dead path-compatibility. Nothing imports it; Mathlib hygiene says delete rather than keep a stub with a "see Core" comment. |

### Public API changes (v0.2)

- `LocalWitness K f t ε` (was `LocalWitness K X f t ε`): drops the
  `X : Type*` parameter and the `[PseudoMetricSpace X]` /
  `[PairableCover X]` instance constraints; drops the `cover`
  field. Retains `neighborhood`, `isOpen_neighborhood`, `t_mem`,
  `replacementEnergy`, `replacementEnergy_continuous`,
  `saving_bound`.
- `class PairableCover X`: **deleted**. `combinedRegion` and
  `diameter_nesting_combined` go with it.
- `exists_refinement`, `exists_sup_reduction`: drop the implicit
  `{X : Type*} [PseudoMetricSpace X] [PairableCover X]` block.
  `witness` hypothesis returns `LocalWitness …` directly (not
  `Nonempty`).
- `exists_sup_reduction_of_cover`: drop `_hδ`, `_hε` arguments.
- `exists_sup_reduction`: drop `_hm_pos` argument.

### Naming alignment with Mathlib

- `f_le_m0` → `f_le_m₀` (Unicode subscript matches the variable).
- `eps_le_sum_saving` → `ε_le_sum_saving`.
- `sup_le_of_saving` → `csSup_range_le_of_pointwise_saving`
  (the `c` prefix flags the conditionally complete sSup; the new
  name reflects the actual hypothesis structure).

### Smoke test pivot

`test/Smoke.lean` previously instantiated `PairableCover` on `ℝ`
with empty regions — a typeclass-instantiation drill with no
mathematical content. With `PairableCover` gone, the smoke test
is rewritten to:

1. construct a non-trivial `LocalWitness` on a constant `f` (the
   replacement is `f` itself, saving zero — but with a positive
   `ε` chosen at the witness-construction site this would be vacuous,
   so we take a piecewise-linear witness instead);
2. assert via `#print axioms` that the public theorems still depend
   only on `propext`, `Classical.choice`, `Quot.sound` (regression
   guard for accidental new axioms).

A non-trivial `LocalWitness` example is also added under
`examples/` so that a downstream reader sees one full instantiation.
