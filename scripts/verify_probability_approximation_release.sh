#!/usr/bin/env bash

set -euo pipefail

workspace=${1:-.}
package="$workspace/.lake/packages/ProbabilityApproximation"
release_tag=v0.9.5
release_commit=26e5a4aff0f117eb5b2ad97d13224fb38dc2f417

case "$(uname -s):$(uname -m)" in
  Darwin:arm64)
    archive=ProbabilityApproximation-arm64-apple-darwin24.6.0.tar.gz
    expected_sha256=06c11571bca3937868a1ca29c374c86c392e906b03dda8e50a16ba592ceb7c08
    ;;
  Linux:x86_64)
    archive=ProbabilityApproximation-x86_64-unknown-linux-gnu.tar.gz
    expected_sha256=ca68954269ae380ef33df181fc2a4e81d2e95c20a9fd859209561ccd0d23ef2b
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

test "$(curl -fsSL https://api.github.com/repos/Polarnova/ProbabilityApproximation/releases/latest |
  jq -r '.tag_name')" = "$release_tag"
test "$(curl -fsSL \
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
