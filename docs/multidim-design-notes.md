# Multi-parameter design notes (v0.7 scaffolding)

This file is **Phase 0 of v0.7**: a desk read of Pitts 1981 §4.8–4.9
(Covering lemmas, p. 159–162) translated into pseudocode aligned with
the parameter-space combinatorial argument that `CombArg/OneDim/`
already formalizes. It documents what Pitts's covering theory carries
over to a pure parameter-space sup-reduction, and what is specific to
the ambient varifold flow and therefore *omitted* from `CombArg`.

It is a **planning document**: it does not commit to any signatures
yet. The signatures it sketches are anchors for Phases 1–5 (see
`docs/design-notes.md` §5 for how this two-tier convention extends
the v0.6 architecture).

The corresponding `docs/design-notes.md` records design decisions
*after* they are made; this file records the reading and translation
work *before* implementation. Once v0.7 ships, surviving load-bearing
decisions from this file migrate into `design-notes.md`; this file
either stays as a historical artifact or is collapsed into a paper
section, mirroring how the 1-param scaffolding evolved.

## §1 Reference and scope

**Canonical reference**: Pitts 1981 *Existence and regularity of
minimal surfaces on Riemannian manifolds*, Princeton, §4.8–4.9
(Covering lemmas), p. 159–162. Local copy at
`resources/Pitts-1981-...pdf`.

**Scope of the m-parameter combinatorial argument**: extend
`CombArg.exists_sup_reduction` from `K = unitInterval` to `K = I^m =
Fin m → unitInterval`. Input: continuous `f : I^m → ℝ`, near-critical
level `N`, a `LocalWitness` at every near-critical point. Output: a
strictly-better continuous competitor `f' ≤ f` agreeing with `f`
outside a small neighborhood of the near-critical set, with `sup f'
< sup f`.

**Out of scope** (lives in OpenGALib or a future
`CombArg/Geometric/`):

- varifold mass `M`, flat metric `F`, support `spt ‖V‖`;
- annuli in the ambient manifold `M` (Pitts's `A(p, s, r)`);
- almost-minimizing predicate, critical sequence definition,
  homotopy classes, $(m, M)$-homotopies;
- §4.10's Theorem itself (the existence of an AM varifold).

The ambient ingredients **enter Pitts §4.10's proof but not §4.8 nor
§4.9** — those two are pure combinatorics on cubical complexes plus a
spacing condition that any spaced family in a metric space satisfies.
That is the wedge that lets `CombArg/MultiDim/` be standalone, the
same way `CombArg/OneDim/` is.

## §2 Pitts §4.8 (greedy disjoint subfamily): translation

### Pitts's statement (paraphrased)

> Let `k, m ∈ ℕ₊`. Let
> `A = { a(p_{ij}, s_{ij}, r_{ij}) : i ∈ [k], j ∈ [km] }`
> be a collection of closed annuli in `ℝⁿ` such that for each `i ∈
> [k]` and each `j ∈ [km - 1]`,
>
> ```
> r_{ij} > s_{ij} > 2 r_{i(j+1)} > 2 s_{i(j+1)}.
> ```
>
> Then there exists a disjoint subcollection `C ⊆ A` such that for
> each `i ∈ [k]`, `card (C ∩ row_i) = m`.

### Proof structure (Pitts p. 159–161)

The proof is a single greedy loop.

```text
function pickDisjoint(A : k × km matrix of annuli with spacing):
    C ← {}; for each i, A_i ← row i of A
    repeat:
        pick (i₀, j₀) such that diam a(i₀, j₀) is minimal in ⋃ A_i
        # spacing ⇒ at most one annulus in any row intersects a(i₀, j₀)
        place a(i₀, j₀) into C_{i₀}
        for each i, A_i ← A_i ∖ { a ∈ A_i : a ∩ a(i₀, j₀) ≠ ∅ }
        if some C_i has size m, discard remaining A_i, loop on others
    until k·m elements selected (loop iterates exactly km times)
    return C = ⋃_i C_i
```

The key invariant: **picking the smallest-diameter annulus removes
at most one annulus per row**, because the spacing factor 2 makes any
two non-adjacent annuli within a row disjoint, and the chosen
annulus's diameter is ≤ the diameter of any annulus it intersects.

### What carries over to parameter-space

Pitts's *spacing condition* `r > s > 2r' > 2s'` is a *metric* fact
about radii, not a varifold fact. It transports verbatim to any
metric space, in particular to `I^m` with the sup metric.

The *annulus* `a(p, s, r) = {x : s ≤ d(x, p) ≤ r}` is just a closed
metric annulus and again works in any metric space. For
`CombArg/MultiDim/` we will use **closed cube cells** of a cubical
grid, not annuli, because the sup-reduction theorem natively wants
*open neighborhoods of near-critical points*, not annuli around
arbitrary points. The spacing condition then becomes the standard
**skip-2 grid spacing**, generalizing 1-param's `SpacedIntervals`.

The *greedy minimal-diameter selection* is purely combinatorial and
maps to a well-founded recursion on the matrix index. Lean
formalization will mirror the 1-param `Stage B` induction in
`OneDim/Induction.lean`.

### What gets dropped

The "annulus-around-a-point" framing is dropped: in our parameter
space, the relevant geometry is *neighborhoods of near-critical
parameters*, not annuli. Pitts uses annuli because his ambient flow
acts on `M`'s tangential annular regions; we never instantiate that.

The condition "annuli are concentric" — Pitts §4.9 strengthens §4.8
by requiring `A(σ)` to be a family of *concentric* closed annuli at a
single center `p` — is not needed in parameter space and is dropped.
We inherit only the spacing factor 2 along *one* dimension (the
refinement hierarchy), not concentricity.

## §3 Pitts §4.9 (face-disjoint cell selection): translation

### Pitts's statement (paraphrased)

> Let `k, m ∈ ℕ₊`. For each `σ ∈ I(m, k)` (a cell of the cubical
> complex `I(m, k)`), let `A(σ)` be a family of `(3^m)·3^m` concentric
> closed annuli at `p_σ ∈ ℝⁿ` satisfying the spacing condition of
> §4.8 (with one row per "magnification" level `r ∈ {1, 2}`).
>
> Then there exists a function `α : I(m, k) → annuli`, with `α(σ) ∈
> A(σ)`, such that whenever `σ ≠ τ` are two faces of a common cell
> `γ ∈ I(m, k)`, the annuli `α(σ)` and `α(τ)` are disjoint.
> Furthermore, `card(image α) ≤ 3^{2m}`.

### Proof structure (Pitts p. 161–162)

The proof is a `3^m`-step nested induction over equivalence classes
of cells.

```text
# Equivalence on I(m, k):
# σ ~ τ iff σ = τ + {x} or τ = σ + {x} for some x ∈ I(m, k-1)₀.
# This partitions I(m, k) into 3^m equivalence classes E_1, …, E_{3^m}.
# Within one class, distinct cells are pairwise disjoint.

# Process classes in order E_1, E_2, …, E_{3^m}.
function selectFaceDisjoint(A):
    α ← ∂  # partial function I(m,k) ⇀ annuli
    for i = 1, 2, …, 3^m:
        for σ ∈ E_i:
            for each face τ of σ:
                # By §4.8 applied to A(τ), reserve a subfamily
                # A_i τ ⊆ A(τ) of size 3^m·(3^m - i),
                # depending only on the equivalence class of τ.
                # Disjointness is maintained: ⋃ A_i τ over τ
                # face-of-σ is disjoint, both within and across faces.
                A_i τ ← reserved subfamily for class i, face τ
                # Invariant: if j < i, then A_i τ ⊆ A_j τ.
        # After step i: every τ has A_i τ ≠ ∅ assigned.
    # After 3^m steps: pick α(τ) ∈ A_{i(τ)} τ where i(τ) is the
    # largest i for which the subfamily is defined.
    return α
```

The crucial bookkeeping: after step `i`, the *intersection* of
already-reserved subfamilies has at least `3^m·(3^m - i)` annuli, so
after `3^m` steps it has at least `3^m·0 + 1 = 1` annulus. (Pitts
phrases the bookkeeping as "subfamily depending only on the
equivalence class of `τ`", which is what makes the nested
restrictions stable across all `σ` in the same class.)

### What carries over

The *cubical equivalence relation* `σ ~ τ ⇔ σ = τ ∪ {x}` is purely
combinatorial. It depends only on `I(m, k)` as an abstract cubical
complex and partitions its cells into `3^m` classes. For Lean this
becomes a `decide`-discharged finite fact about `Fin (3^m)`-coloring
of cells.

The *face-of-cell* relation `γ` is again purely combinatorial: a
cell `τ` is a face of `γ` iff `τ`'s coordinate intervals are all
faces (= edges or vertices in the relevant dimension) of `γ`'s. This
maps to `Decidable` on `Fin m → {0, 1, [0,1]}`-style cell encodings.

The *3^m-step nested induction* itself is combinatorial; Lean
formalization is a `Fin (3^m)`-indexed `Nat.rec` where each step
narrows a per-class subfamily by §4.8.

The *image multiplicity* bound `card (image α) ≤ 3^{2m}` is the
multi-parameter analog of 1-param's `twoFold_closure ≤ 2`. This is
the number that becomes the new `multiplicityBound` field in
`FiniteCoverWithWitnesses` (see §6 below for the prerequisite
refactor).

### What gets dropped

The annuli themselves drop out, replaced by **cube cells** in the
parameter space. The "concentric at `p_σ`" requirement disappears:
in parameter space, each cube cell already has its own center
naturally, and the §4.8 spacing replaces "concentric subfamily" with
"chain of nested sub-cubes" — same combinatorial content, simpler
geometry.

Pitts's "magnification levels `r ∈ {1, 2}`" (the auxiliary index in
his §4.9) reflects ambient-flow sensitivity to scale of annuli; we
do not have an ambient flow, so this index drops out and the
collection size shrinks from `(3^m)·3^m` to `3^m·m`.

## §4 Mapping table (1-param ↔ m-param)

The extant `OneDim/` skeleton already has the right shape; the
`MultiDim/` skeleton echoes it.

| 1-param `OneDim/` | m-param `MultiDim/` | Pitts cross-ref |
|---|---|---|
| `K = unitInterval` | `K = Fin m → unitInterval` | §4.4(2) |
| `SpacedIntervals` (skip-2 along `Fin n`) | `SpacedCells` (skip-2 along each axis of cubical grid) | §4.8 spacing |
| `InitialCover.lean` (Stage A: cells + witnesses) | `CubicalCover.lean` (cube cells of `I(m,k)` + witnesses) | §4.4(3-5) |
| `PartialRefinement.lean` (Stage B: J + σ) | `FaceDisjointSelection.lean` (Pitts `α`) | §4.9 |
| `Induction.lean` (smallest-index recursion) | `Induction.lean` (3^m-step nested recursion over equiv classes) | §4.9 PROOF |
| `not_three_overlap_any_order` | `face_disjoint_image` | §4.9 conclusion |
| `twoFold_closure ≤ 2` | `multiplicity_closure ≤ 3^m` (or m+1, see §7) | §4.9 last line |
| `DLTCover` (structured Stage A+B output) | `MultiDimCover` (same role, multi-param) | — |
| `DLTCover.toFinite` | `MultiDimCover.toFinite` | — |

**Reuse with zero changes**:

- `CombArg/Witness.lean` — `LocalWitness` is already `(K : Type*)
  [TopologicalSpace K]`-generic. No changes.
- `CombArg/Common/NearCritical.lean` — `nearCritical f m₀ N` is also
  `K`-generic. The compactness/non-emptiness lemmas need
  `[CompactSpace K]`, which `Fin m → unitInterval` instantiates from
  Mathlib. No changes.
- `CombArg/Common/SavingClosure.lean` — `K`-generic. No changes.
- `CombArg/SupReduction.lean` (the `K`-generic
  `exists_sup_reduction_of_cover` corollary) — already `K`-generic
  except for the `multiplicityBound = 2` hardcode in the saving
  arithmetic. **One refactor needed**, see §6.

**No reuse from `OneDim/` nor `Scalar/`**: the multi-parameter
combinatorics is a parallel sister namespace, not a generalization.
The 1-param public API stays bit-stable.

## §5 Folder structure (proposed)

```text
CombArg/MultiDim/
├── ParameterSpace.lean       # I^m = Fin m → unitInterval; CompactSpace,
│                             # MetricSpace instances, basic lemmas
├── CubicalGrid.lean          # I(m,k) cells, faces, equivalence classes,
│                             # decidability
├── SpacedCells.lean          # §4.8 spacing condition + greedy disjoint
│                             # subfamily extraction (the Pitts §4.8 lemma)
├── CubicalCover.lean         # Stage A: pin a LocalWitness to each
│                             # near-critical cube cell
├── FaceDisjointSelection.lean  # §4.9 selection function α; the 3^m-step
│                               # nested induction over equiv classes
├── Induction.lean            # The 3^m-step recursion proper, factored
│                             # for testability (1-param test case = m=1)
├── ParityRescue.lean         # multiplicity_closure ≤ 3^m, via
│                             # face_disjoint_image + closure topology
├── MultiDimCover.lean        # Structured output: initialCover + selection
│                             # + invariants. Mirror of OneDim/DLTCover.
└── Assembly.lean             # exists_MultiDimCover (Stage A + B)
                              # exists_refinement_md = (...).toFinite
```

**Conventions**:

- All files use `namespace CombArg.MultiDim` (mirroring
  `CombArg.OneDim`).
- Public theorems exposed at the namespace root:
  `exists_sup_reduction_md` (the m-parameter analog of
  `CombArg.exists_sup_reduction`).
- The `MultiDimCover` structure follows `DLTCover`'s shape exactly,
  with the bookkeeping field renamed from `σ_injective` to whatever
  Pitts §4.9 ends up naming the face-disjointness invariant.
- `_md` suffix on public names disambiguates from 1-param public
  names; downstream code can `open CombArg.MultiDim` if it wants to
  drop the suffix.

## §6 Prerequisite refactor: parametrize `multiplicityBound`

The blocker for v0.7 Phase 1 is `CombArg/Cover.lean`'s hardcoded
two-fold:

```lean
structure FiniteCoverWithWitnesses ... where
  ...
  twoFold : ∀ t, (Finset.univ.filter (fun i => t ∈ piece i)).card ≤ 2
```

The arithmetic in `exists_sup_reduction_of_cover` works because the
total-saving accumulator is bounded by `2 · saving = 1/(2N) <
1/N = δ`. For `multiplicityBound = k`, the same accumulator becomes
`k · saving`, so we must either:

(a) **Strengthen `saving` per-cover**: keep `multiplicityBound = 2`
hardcoded, but require the cover-producer to deliver
`saving = 1/(2k·N)` instead of `1/(4N)`. This pushes complexity into
the m-param Pitts machinery and inflates the "effective near-critical
margin" from `1/N` to `1/(k·N)`, which downstream consumers may or
may not tolerate.

(b) **Parametrize `multiplicityBound`**: add a field
`multiplicityBound : ℕ` to `FiniteCoverWithWitnesses` and rewrite
`exists_sup_reduction_of_cover`'s saving arithmetic in terms of
`multiplicityBound`. The 1-param call sites pass `multiplicityBound
:= 2` and the saving threshold stays at `1/(4N)`. The m-param call
site passes `multiplicityBound := 3^m` (or `m+1`, see §7) and the
required `saving` field for compatibility scales accordingly.

**Decision**: go with (b). It keeps 1-param public API unchanged
(default the new field with `:= 2` in 1-param call sites) and gives
m-param the room it needs. The arithmetic in `SupReduction.lean`
will become:

```lean
-- For each t, the per-piece saving sums dominate the total drop:
have h_total : multiplicityBound * saving ≤ ... := ...
have h_drop : ... ≥ saving / 2 := ...   -- depends only on saving
```

Concretely the inner `linarith` step in `SupReduction.lean` should
just consume `multiplicityBound * saving < δ` instead of `2 * saving
< δ`, with the cover-producer responsible for ensuring the inequality.

The 1-param `Audit.lean` baseline must stay unchanged after the
refactor; that is the regression check for Phase 1.

## §7 Open question: `3^m` vs `m+1` multiplicity

Pitts §4.9 gives `card (image α) ≤ 3^{2m}` (here `3^m` after
dropping the magnification index). This is far worse than the
**Lebesgue covering dimension** bound `m+1`: any open cover of
`I^m` admits an open refinement with order `≤ m+1`.

**Why Pitts uses 3^m**: the cubical / face-disjoint structure is
needed because his §4.10 proof acts the homotopy *cell by cell* on
`I(m,k)`, and face-adjacent cells must avoid interfering. A
multiplicity bound alone (the Lebesgue version) does not give this
structural property; Pitts therefore pays the price of `3^m` to keep
the cubical adjacency.

**For sup-reduction alone**, the structural property is unused:
`exists_sup_reduction_of_cover` only needs `multiplicityBound`, not
adjacency. So a *Tier 2 multi-param scalar path* (analogous to
`CombArg/Scalar/Partition.lean` for 1-param) could give
`multiplicityBound = m+1` via Lebesgue dimension.

**v0.7 plan**: implement only the Pitts-faithful path
(`multiplicityBound = 3^m`). The structural output `MultiDimCover`
is kept for downstream geometric consumers in OpenGALib who may want
the cubical adjacency. A Tier 2 `MultiDim/Scalar/` Lebesgue-dimension
path is deferred to v0.8 (analogous to v0.4 introducing
`Scalar/Partition.lean` only after the DLT path was solid).

This is the same two-tier convention `docs/design-notes.md` §5
documents for 1-param. The trade-off is identical: structure-bearing
vs cheap, with the architectural claim verified by dependency-graph
strict separation (Finding F7 in `design-notes.md`).

## §8 Risks and unknowns

**R1. Cubical complex Mathlib coverage.** Mathlib has `CWComplex`
and `SimplicialComplex` but not a first-class cubical complex. The
`I(m, k)` index set for our purposes is small enough to encode
directly as `Fin (k+1)^m` with explicit face/equivalence
combinatorics (decidable, `omega`-discharged). This is acceptable
boilerplate but adds ~150–300 lines of pure index combinatorics to
`CubicalGrid.lean`. **No load-bearing dependency on cubical-complex
infrastructure beyond what we hand-roll.**

**R2. Pitts §4.9 proof formalization length.** Pitts's prose for
the 3^m-step induction is dense (≈1.5 pages, p. 161–162). My
estimate is 350–500 Lean lines for `FaceDisjointSelection.lean`,
mostly bookkeeping for the per-class reserved subfamilies. If it
balloons past 700 lines, split into `FaceDisjointSelection/` with
files for (a) equivalence classes, (b) per-class subfamily induction,
(c) extraction of α.

**R3. `multiplicity_closure ≤ 3^m` proof.** The 1-param analog
needed an `omega`-discharged "among any 3 indices, two are
even-gapped" parity rescue (Finding F4). The m-param analog needs to
chase the cell-adjacency structure through closure topology. Pitts
does not give this in §4.9 — he hands it to §4.10. We will need to
state it ourselves; expected proof length 50–150 Lean lines.

**R4. v0.7 timeline.** Phase 1 (Algo-A1 refactor) is small (≤ 1
day). Phase 2 (`ParameterSpace`, `CubicalGrid`) is mostly
bookkeeping, ≤ 2 days. Phase 3 (`SpacedCells` = §4.8) is moderate, ≤
3 days. Phase 4 (`FaceDisjointSelection` + `Induction` = §4.9) is
the bulk, 5–10 days. Phase 5 (`MultiDimCover` + `Assembly` +
`ParityRescue`) is wiring, ≤ 3 days. Phase 6 (audit, paper sync,
release) is ≤ 1 day. Total ≈ 15–20 person-days, with §4.9 the long
pole.

## §9 Phase exit criteria

| Phase | Exit criterion |
|---|---|
| 0 | This file (`docs/multidim-design-notes.md`) committed. |
| 1 | `multiplicityBound : ℕ` field in `FiniteCoverWithWitnesses`; 1-param `Audit.lean` baseline unchanged. |
| 2 | `lake build CombArg.MultiDim.CubicalGrid` succeeds, no `sorry`. |
| 3 | `lake build CombArg.MultiDim.SpacedCells` succeeds, no `sorry`; `m=1` instantiation regression-tests against `OneDim.SpacedIntervals` for non-triviality. |
| 4 | `lake build CombArg.MultiDim.FaceDisjointSelection` succeeds; `card_image_le` produces `≤ 3^m`. |
| 5 | `CombArg.MultiDim.exists_sup_reduction_md` available; m=1 specialization equals `CombArg.exists_sup_reduction`. |
| 6 | `Audit.lean` extended for new public theorems; `paper/sections/future.tex` §6.2 promoted to `paper/sections/multidim.tex`. |

After Phase 6: tag v0.7.0, sync to GitHub, sync to Overleaf.
