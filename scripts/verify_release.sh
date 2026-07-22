#!/usr/bin/env bash

set -euo pipefail

workspace="$(cd "${1:-.}" && pwd)"
manifest="$workspace/lake-manifest.json"

test -f "$manifest"

release_tag="$(jq -er '.packages[] | select(.name == "FABL") | .inputRev' "$manifest")"
release_commit="$(jq -er '.packages[] | select(.name == "FABL") | .rev' "$manifest")"
packages_dir="$(jq -r '.packagesDir // ".lake/packages"' "$manifest")"
package="$(cd "$workspace" && cd "$packages_dir/FABL" && pwd)"

[[ "$release_tag" =~ ^v[0-9]+\.[0-9]+\.[0-9]+$ ]]
test -d "$package/.git"
test "$(git -C "$package" rev-parse HEAD)" = "$release_commit"

release_url="https://github.com/Polarnova/FABL/releases/download/$release_tag"
matching_traces=()
for trace in "$package"/.lake/FABL-*.tar.gz.trace; do
  if [[ -f "$trace" ]] && grep -Fq "$release_url/" "$trace"; then
    matching_traces+=("$trace")
  fi
done
test "${#matching_traces[@]}" -eq 1

trace_path="${matching_traces[0]}"
archive_path="${trace_path%.trace}"
archive="$(basename "$archive_path")"
test -f "$archive_path"

curl_args=(-fsSL -H "Accept: application/vnd.github+json")
if [[ -n "${GH_TOKEN:-}" ]]; then
  curl_args+=(-H "Authorization: Bearer $GH_TOKEN")
fi
release_json="$(curl "${curl_args[@]}" \
  "https://api.github.com/repos/Polarnova/FABL/releases/tags/$release_tag")"
expected_digest="$(jq -er --arg archive "$archive" \
  '.assets[] | select(.name == $archive) | .digest' <<<"$release_json")"
[[ "$expected_digest" =~ ^sha256:[0-9a-f]{64}$ ]]

if command -v sha256sum >/dev/null 2>&1; then
  sha256() { sha256sum "$1" | awk '{print $1}'; }
  sha256_stream() { sha256sum | awk '{print $1}'; }
else
  sha256() { shasum -a 256 "$1" | awk '{print $1}'; }
  sha256_stream() { shasum -a 256 | awk '{print $1}'; }
fi

test "sha256:$(sha256 "$archive_path")" = "$expected_digest"

for module in \
  FABL.olean \
  FABL/Chapter01/CubeCardinality.olean \
  FABL/Chapter06/F₂Polynomials/ANF.olean
do
  tar -tzf "$archive_path" "./lib/lean/$module" >/dev/null
  extracted_module="$package/.lake/build/lib/lean/$module"
  test -f "$extracted_module"
  archive_module_sha256="$(tar -xOzf "$archive_path" "./lib/lean/$module" | sha256_stream)"
  extracted_module_sha256="$(sha256 "$extracted_module")"
  test "$archive_module_sha256" = "$extracted_module_sha256"
done

printf 'Verified FABL %s release archive: %s\n' "$release_tag" "$archive"
