# resources/

Local reference material for working on the paper and library.
**PDFs in this directory are gitignored** (see the repo
`.gitignore`): they are copyrighted and kept locally only.

## Expected contents

| File / directory | Source |
|---|---|
| `Pitts-1981-Existence-and-regularity-of-minimal-surfaces-on-Riemannian-manifolds.pdf` | J. T. Pitts, Mathematical Notes 27, Princeton University Press, 1981. Obtain a legitimate copy from your institution's library. |
| `DLT13-source/` | arXiv source of De~Lellis--Tasnady, *The existence of embedded minimal hypersurfaces* (arXiv:0905.4192 → J. Differential Geom. 95 (2013) 3, 355--388). Fetch with `curl -sL https://arxiv.org/e-print/0905.4192 \| tar -xz -C resources/DLT13-source/`. |

## Adding new references

- **PDFs**: drop into this directory with a filename of the form
  `<AuthorYear>-<short-title>.pdf`. The gitignore rule
  `resources/*.pdf` keeps it out of version control.
- **arXiv sources**: extract into `resources/<AuthorYear>-source/`.
  The gitignore rule `resources/*-source/` keeps them out of
  version control.

This `README.md` is tracked; update the table above if you add a
new reference collaborators are expected to fetch.
