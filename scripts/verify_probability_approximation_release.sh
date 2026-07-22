#!/usr/bin/env bash

set -euo pipefail

workspace="$(cd "${1:-.}" && pwd)"
manifest="$workspace/lake-manifest.json"
packages_dir="$(jq -r '.packagesDir // ".lake/packages"' "$manifest")"
package="$(cd "$workspace" && cd "$packages_dir/ProbabilityApproximation" && pwd)"
release_tag=v0.9.6
release_commit=c89fba908a33ba741836407f43c67609e2d05279

case "$(uname -s):$(uname -m)" in
  Darwin:arm64)
    archive=ProbabilityApproximation-arm64-apple-darwin24.6.0.tar.gz
    expected_sha256=a22c7da332c174d739f33e90e68f48a79fbec65b0cde1673776993c4260cc918
    ;;
  Linux:x86_64)
    archive=ProbabilityApproximation-x86_64-unknown-linux-gnu.tar.gz
    expected_sha256=ae9fe85ed1d8222c3b165e383279b05075974c43465ed352c56eb025e212dbc7
    ;;
  *)
    printf 'ProbabilityApproximation %s has no pinned release asset for %s/%s\n' \
      "$release_tag" "$(uname -s)" "$(uname -m)" >&2
    exit 1
    ;;
esac

archive_path="$package/.lake/$archive"
trace_path="$archive_path.trace"
release_url="https://github.com/Polarnova/ProbabilityApproximation/releases/download/$release_tag/$archive"

curl_args=(-fsSL -H "Accept: application/vnd.github+json")
if [[ -n "${GH_TOKEN:-}" ]]; then
  curl_args+=(-H "Authorization: Bearer $GH_TOKEN")
fi

test "$(curl "${curl_args[@]}" \
  https://api.github.com/repos/Polarnova/ProbabilityApproximation/releases/latest |
  jq -r '.tag_name')" = "$release_tag"
test "$(curl "${curl_args[@]}" \
  "https://api.github.com/repos/Polarnova/ProbabilityApproximation/releases/tags/$release_tag" |
  jq -r --arg archive "$archive" '.assets[] | select(.name == $archive) | .digest')" = \
  "sha256:$expected_sha256"

test -d "$package/.git"
test "$(git -C "$package" rev-parse HEAD)" = "$release_commit"
test -f "$archive_path"
test -f "$trace_path"
grep -Fq "$release_url" "$trace_path"

if command -v sha256sum >/dev/null 2>&1; then
  actual_sha256=$(sha256sum "$archive_path" | awk '{print $1}')
else
  actual_sha256=$(shasum -a 256 "$archive_path" | awk '{print $1}')
fi
test "$actual_sha256" = "$expected_sha256"

for module in \
  ProbabilityApproximation/Bentkus/Induction.olean \
  ProbabilityApproximation/ChenShao/UniformBerryEsseen.olean \
  ProbabilityApproximation/ChenShao/NonuniformBerryEsseen.olean
do
  tar -tzf "$archive_path" "./lib/lean/$module" >/dev/null
  extracted_module="$package/.lake/build/lib/lean/$module"
  test -f "$extracted_module"
  if command -v sha256sum >/dev/null 2>&1; then
    archive_module_sha256=$(tar -xOzf "$archive_path" "./lib/lean/$module" | sha256sum | awk '{print $1}')
    extracted_module_sha256=$(sha256sum "$extracted_module" | awk '{print $1}')
  else
    archive_module_sha256=$(tar -xOzf "$archive_path" "./lib/lean/$module" | shasum -a 256 | awk '{print $1}')
    extracted_module_sha256=$(shasum -a 256 "$extracted_module" | awk '{print $1}')
  fi
  test "$archive_module_sha256" = "$extracted_module_sha256"
done

printf 'Verified ProbabilityApproximation %s release archive: %s\n' "$release_tag" "$archive"
