# `CombArg/Geometric/` — geometric-lift consumers (placeholder)

This directory is reserved for future geometric consumers of the
`OneDim.DLTCover` structure. The intended occupants are:

* `ModifiedSweepout.lean` — the De Lellis–Tasnady modified-sweepout
  construction, lifted from a `DLTCover` to a continuous family of
  ambient currents `{∂Ω'_t}` via blending on the positive-measure
  overlap regions `J_i ∩ J_{i+1}`. This requires the spacing /
  overlap structure that `DLTCover` exposes and that the
  `Scalar.Partition` route deliberately discards.

`v0.4` ships only the architecture (the abstract two-tier API
under `OneDim/` and `Scalar/`); the geometric tier is intentionally
empty for v0.4 and is the planned subject of a future release.

See `paper/sections/intro.tex` Remark 1.5
(`rem:why-construction`) for the design rationale connecting this
empty directory to the `DLTCover` overlap structure that the
construction in `OneDim/` preserves.
