#!/usr/bin/env bash
# Regenerate docs/import-graph.{dot,svg}.
# Requires: lake (for the importGraph package via Mathlib) and
# graphviz (for SVG rendering). On macOS: `brew install graphviz`.

set -euo pipefail

cd "$(dirname "$0")/.."

echo "Generating dot..."
lake exe graph --to CombArg --exclude-meta docs/import-graph.dot

if command -v dot >/dev/null 2>&1; then
  echo "Rendering SVG..."
  dot -Tsvg docs/import-graph.dot -o docs/import-graph.svg
  echo "Wrote docs/import-graph.svg"
else
  echo "Note: graphviz 'dot' not found; SVG not regenerated."
  echo "Install with: brew install graphviz  (macOS)"
  echo "             apt install graphviz   (Debian/Ubuntu)"
fi
