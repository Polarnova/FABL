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
    | [$blocks[] | select(any(.tags[]; startswith("section-1-")))] as $chapter1
    | [$blocks[] | select(any(.tags[]; startswith("section-2-")))] as $chapter2
    | [$blocks[] | select(any(.tags[]; startswith("section-3-")))] as $chapter3
    | [$blocks[] | select(any(.tags[]; startswith("section-4-")))] as $chapter4
    | [$blocks[] | select(any(.tags[]; startswith("section-5-")))] as $chapter5
    | [$blocks[] | .codeData.external.decls[]?] as $decls
    | [.previews[] | select(.targetKind == "leanDecl")] as $leanDecls
    | .graphs[0] as $graph
    | (.vbpInternalSchemaVersion == 2)
      and (($blocks | length) == 337)
      and (($chapter1 | length) == 43)
      and (($chapter2 | length) == 79)
      and (($chapter3 | length) == 62)
      and (($chapter4 | length) == 45)
      and (($chapter5 | length) == 108)
      and (all($blocks[];
        ([.tags[]
          | select(startswith("section-1-") or startswith("section-2-")
            or startswith("section-3-") or startswith("section-4-")
            or startswith("section-5-"))]
          | length) == 1))
      and ((.previews | length) == (($blocks | length) + ($leanDecls | length)))
      and (($leanDecls | length) == ($decls | length))
      and (([$blocks[].leanCodePreviewKeys[]] | length) == ($decls | length))
      and (([$blocks[].leanCodePreviewKeys[]] | unique | length) == ($decls | length))
      and (([$blocks[].leanCodePreviewKeys[]] | sort) == ([$leanDecls[].key] | sort))
      and (([$decls[].canonical] | unique | length) == ($decls | length))
      and (all($decls[];
        .present == true
        and .provedStatus == "proved"
        and (.render | has("ok"))))
      and (all($blocks[]; (.tags | length) > 0 and .sourceLocation.ok == true))
      and (([$blocks[] | select(.tags | index("support"))] | length) == 110)
      and (([$blocks[] | select((.tags | index("support")) == null)] | length) == 227)
      and (([$chapter1[] | select(.tags | index("support"))] | length) == 9)
      and (([$chapter2[] | select(.tags | index("support"))] | length) == 15)
      and (([$chapter3[] | select(.tags | index("support"))] | length) == 19)
      and (([$chapter4[] | select(.tags | index("support"))] | length) == 8)
      and (([$chapter5[] | select(.tags | index("support"))] | length) == 59)
      and (([$chapter1[] | .codeData.external.decls | length] | add) == 111)
      and (([$chapter2[] | .codeData.external.decls | length] | add) == 241)
      and (([$chapter3[] | .codeData.external.decls | length] | add) == 399)
      and (([$chapter4[] | .codeData.external.decls | length] | add) == 360)
      and (([$chapter5[] | .codeData.external.decls | length] | add) == 502)
      and (([$blocks[] | .statementUses | length] | add) == 781)
      and (([$chapter1[] | .statementUses | length] | add) == 62)
      and (([$chapter2[] | .statementUses | length] | add) == 185)
      and (([$chapter3[] | .statementUses | length] | add) == 164)
      and (([$chapter4[] | .statementUses | length] | add) == 111)
      and (([$chapter5[] | .statementUses | length] | add) == 259)
      and (([$blocks[] | .proofUses | length] | add) == 0)
      and (([$blocks[] | .uses | length] | add) == 781)
      and (([$blocks[] | .usedBy | length] | add) == 781)
      and ((.graphs | length) == 1)
      and (($graph.nodes | length) == 337)
      and (([$graph.nodes[].label] | unique | length) == 337)
      and (([$graph.nodes[].previewKey] | unique | length) == 337)
      and (($graph.edges | length) == 781)
      and (all($graph.edges[]; .axes == ["statement"]))
      and (all($graph.nodes[];
        .warnings.leanOnlyNoStatement == false
        and .warnings.missingExternalDecl == false
        and .warnings.unknownRef == false))
      and (all($chapter1[];
        .key as $key
        | any($graph.nodes[];
            .previewKey == $key
            and .statementStatus == "formalized"
            and .proofStatus == "formalizedWithAncestors")))
      and (all($chapter2[];
        .key as $key
        | any($graph.nodes[];
            .previewKey == $key
            and .statementStatus == "formalized"
            and .proofStatus == "formalizedWithAncestors")))
      and (all($blocks[];
        .key as $key
        | (.codeData.external.decls | length) as $associated
        | any($graph.nodes[];
            .previewKey == $key
            and (if $associated > 0 then
              .statementStatus == "formalized"
              and (.proofStatus == "formalized"
                or .proofStatus == "formalizedWithAncestors")
            else
              ((.statementStatus == "ready" and .proofStatus == "ready")
                or (.statementStatus == "blocked" and .proofStatus == "none"))
            end))))
  ' "$manifest" >/dev/null || {
    echo "generated Blueprint failed the coverage, declaration-link, or status checks" >&2
    exit 1
  }

  "$lake_cmd" exe vbp check --site "$output" >/dev/null
}

build_site() {
  build_library
  echo "Rendering Blueprint HTML..."
  rm -rf -- "$output/html-multi"
  export FABL_SOURCE_REVISION="${GITHUB_SHA:-$(git -C "$root/.." rev-parse HEAD)}"
  export PROBABILITY_APPROXIMATION_SOURCE_REVISION="$(
    git -C "$root/.lake/packages/ProbabilityApproximation" rev-parse HEAD
  )"
  export MATHLIB_SOURCE_REVISION="$(
    git -C "$root/.lake/packages/mathlib" rev-parse HEAD
  )"
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
