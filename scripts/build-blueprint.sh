#!/usr/bin/env bash
# Build the leanblueprint web version and extract the dependency
# graph DOT/SVG into docs/blueprint-graph.{dot,svg} for embedding
# in README.md.
#
# Requirements:
#   * pip3 install --user leanblueprint
#       (with `CFLAGS=-I$(brew --prefix graphviz)/include
#              LDFLAGS=-L$(brew --prefix graphviz)/lib`
#        on macOS so pygraphviz finds Homebrew graphviz headers).
#   * graphviz (`brew install graphviz` / `apt install graphviz`).
#   * `$HOME/Library/Python/3.9/bin` on PATH (macOS pip --user
#     install location).

set -euo pipefail

cd "$(dirname "$0")/.."

if ! command -v leanblueprint >/dev/null 2>&1; then
  PY_USER_BIN="${HOME}/Library/Python/3.9/bin"
  if [ -x "${PY_USER_BIN}/leanblueprint" ]; then
    export PATH="${PY_USER_BIN}:${PATH}"
  else
    echo "Error: leanblueprint not on PATH; install via 'pip3 install --user leanblueprint'."
    exit 1
  fi
fi

pushd blueprint > /dev/null
rm -rf web web.paux src/web.paux
leanblueprint web > /tmp/leanblueprint-web.log 2>&1
popd > /dev/null

# Pull the inline DOT data out of the rendered HTML and re-render
# with `dot` to a standalone SVG that GitHub README can embed.
grep -oE 'strict digraph[^`]*' \
  blueprint/web/dep_graph_document.html \
  | head -1 > docs/blueprint-graph.dot
dot -Tsvg docs/blueprint-graph.dot -o docs/blueprint-graph.svg

echo "Wrote docs/blueprint-graph.{dot,svg}"
echo "Full blueprint web version is at blueprint/web/index.html"
echo "(serve with 'leanblueprint serve' from blueprint/)."
