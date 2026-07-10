#!/usr/bin/env bash

set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
output="$root/_out/site"
book_output="$root/_out/book"

if command -v lake >/dev/null 2>&1; then
  lake_cmd="$(command -v lake)"
elif [[ -x "$HOME/.elan/bin/lake" ]]; then
  lake_cmd="$HOME/.elan/bin/lake"
else
  echo "lake is not available on PATH or under \$HOME/.elan/bin" >&2
  exit 127
fi

build_library() {
  cd "$root"
  echo "Checking compiled Blueprint modules with Lake..."
  "$lake_cmd" build FABLBlueprint
}

validate_site() {
  local manifest="$output/html-multi/-verso-data/blueprint-manifest.json"

  if ! command -v jq >/dev/null 2>&1; then
    echo "jq is required to validate the generated Blueprint" >&2
    exit 127
  fi

  jq -e '
    [.previews[] | select(.targetKind == "block" and .facet == "statement")] as $blocks
    | [$blocks[] | .codeData.external.decls[]?] as $decls
    | .graphs[0] as $graph
    | (.vbpInternalSchemaVersion == 2)
      and ((.previews | length) == 144)
      and (($blocks | length) == 41)
      and (([.previews[] | select(.targetKind == "leanDecl")] | length) == 103)
      and (all($blocks[]; (.codeData.external.decls | length) > 0))
      and (([$blocks[].leanCodePreviewKeys[]] | length) == 103)
      and (([$blocks[].leanCodePreviewKeys[]] | unique | length) == 103)
      and (($decls | length) == 103)
      and (([$decls[].canonical] | unique | length) == 103)
      and (all($decls[];
        .present == true
        and .provedStatus == "proved"
        and (.render | has("ok"))))
      and (all($blocks[]; (.tags | length) > 0 and .sourceLocation.ok == true))
      and (([$blocks[] | select(.tags | index("support"))] | length) == 7)
      and (([$blocks[] | select((.tags | index("support")) == null)] | length) == 34)
      and (([$blocks[] | .statementUses | length] | add) == 59)
      and (([$blocks[] | .proofUses | length] | add) == 0)
      and (([$blocks[] | .uses | length] | add) == 59)
      and (([$blocks[] | .usedBy | length] | add) == 59)
      and ((.graphs | length) == 1)
      and (($graph.nodes | length) == 41)
      and (($graph.edges | length) == 59)
      and (all($graph.edges[]; .axes == ["statement"]))
      and (all($graph.nodes[];
        .statementStatus == "formalized"
        and .proofStatus == "formalizedWithAncestors"
        and .warnings.leanOnlyNoStatement == false
        and .warnings.missingExternalDecl == false
        and .warnings.unknownRef == false))
  ' "$manifest" >/dev/null || {
    echo "generated Blueprint failed the Chapter 1 coverage and declaration-link checks" >&2
    exit 1
  }

  "$lake_cmd" exe vbp check --site "$output" >/dev/null
}

build_site() {
  build_library
  echo "Rendering Blueprint HTML..."
  "$lake_cmd" lean FABLBlueprintMain.lean -- --run FABLBlueprintMain.lean --output "$output"
  test -f "$output/html-multi/index.html"
  test -f "$output/html-multi/-verso-data/blueprint-manifest.json"
  test -f "$output/html-multi/-verso-data/blueprint-html-cache.json"
  validate_site
}

build_pdf() {
  build_library
  echo "Rendering the book PDF..."
  "$lake_cmd" lean FABLBookMain.lean -- --run FABLBookMain.lean \
    --output "$book_output" --without-html-multi --pdf
  test -f "$book_output/pdf/main.pdf"
  mkdir -p "$output/pdf"
  cp "$book_output/pdf/main.pdf" "$output/pdf/main.pdf"
}

case "${1:-build}" in
  build)
    build_site
    ;;
  serve)
    build_site
    exec python3 -m http.server --directory "$output/html-multi" "${PORT:-8000}"
    ;;
  pdf)
    build_pdf
    ;;
  *)
    echo "usage: $0 [build|serve|pdf]" >&2
    exit 2
    ;;
esac
