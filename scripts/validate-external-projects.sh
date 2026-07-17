#!/usr/bin/env bash

set -u
set -o pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)" || exit 1
readonly SCRIPT_DIR
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)" || exit 1
readonly REPO_ROOT
readonly FORMATTER="$REPO_ROOT/.lake/build/bin/fmt"
readonly WORK_DIR="${LEANFMT_VALIDATION_DIR:-$REPO_ROOT/.scratch/external-validation}"
readonly FILES_PER_BATCH="${LEANFMT_VALIDATION_BATCH_SIZE:-200}"

declare -a DEFAULT_PROJECTS=(
  "cslib|https://github.com/leanprover/cslib.git"
  "mathlib|https://github.com/leanprover-community/mathlib4.git"
)

failures=0

section() {
  printf '\n==> %s\n' "$1"
}

run_phase() {
  local description="$1"
  shift
  local started_at=$SECONDS

  section "$description"
  if "$@"; then
    printf 'PASSED (%ds): %s\n' "$((SECONDS - started_at))" "$description"
    return 0
  else
    local status=$?
    printf 'FAILED (exit %d, %ds): %s\n' \
      "$status" "$((SECONDS - started_at))" "$description" >&2
    failures=$((failures + 1))
    return 0
  fi
}

run_optional_phase() {
  local description="$1"
  shift
  local started_at=$SECONDS

  section "$description"
  if "$@"; then
    printf 'PASSED (%ds): %s\n' "$((SECONDS - started_at))" "$description"
  else
    local status=$?
    printf 'SKIPPED (exit %d, %ds): %s\n' \
      "$status" "$((SECONDS - started_at))" "$description" >&2
  fi
}

clone_project() {
  local url="$1"
  local destination="$2"

  rm -rf "$destination"
  git clone --depth 1 "$url" "$destination"
}

get_build_cache() {
  local project_dir="$1"

  if [[ "${LEANFMT_VALIDATION_SKIP_CACHE:-0}" == "1" ]]; then
    printf 'Skipping the Lake build cache (LEANFMT_VALIDATION_SKIP_CACHE=1).\n'
    return 0
  fi

  (cd "$project_dir" && lake exe cache get)
}

build_project() {
  local project_dir="$1"
  (cd "$project_dir" && lake build)
}

run_formatter() {
  local project_dir="$1"
  shift
  local -a files=()
  local file

  while IFS= read -r -d '' file; do
    files+=("$project_dir/$file")
  done < <(git -C "$project_dir" ls-files -z -- '*.lean')

  if ((${#files[@]} == 0)); then
    return 0
  fi

  # Keep the formatter in this repository's toolchain context. Running it from
  # the external project can make Elan select an incompatible Lean toolchain.
  (
    cd "$REPO_ROOT" || exit 1
    printf '%s\0' "${files[@]}" |
      xargs -0 -n "$FILES_PER_BATCH" "$FORMATTER" "$@"
  )
}

main() {
  local started_at=$SECONDS
  local -a projects=("${DEFAULT_PROJECTS[@]}")
  if (($# > 0)); then
    projects=()
    local specification
    for specification in "$@"; do
      if [[ "$specification" != *=* ]]; then
        printf 'Invalid project %q; expected NAME=GIT_URL_OR_PATH.\n' \
          "$specification" >&2
        return 2
      fi
      projects+=("${specification%%=*}|${specification#*=}")
    done
  fi

  mkdir -p "$WORK_DIR"

  run_phase "Build leanfmt" lake build fmt
  if [[ ! -x "$FORMATTER" ]]; then
    printf 'Cannot continue without the formatter executable: %s\n' "$FORMATTER" >&2
    exit 1
  fi

  local project name url project_dir
  for project in "${projects[@]}"; do
    IFS='|' read -r name url <<< "$project"
    project_dir="$WORK_DIR/$name"

    run_phase "Clone $name" clone_project "$url" "$project_dir"
    if [[ ! -d "$project_dir/.git" ]]; then
      printf 'Skipping %s because its clone is unavailable.\n' "$name" >&2
      continue
    fi

    run_optional_phase "Download $name build cache" get_build_cache "$project_dir"
    run_phase "Build $name before formatting" build_project "$project_dir"
    run_phase "Format $name and validate exceptions/idempotence" \
      run_formatter "$project_dir" --check-exception --check-idempotent
    run_phase "Build $name after formatting" build_project "$project_dir"
  done

  section "Validation summary"
  if ((failures == 0)); then
    printf 'All external validation phases passed in %ds.\n' \
      "$((SECONDS - started_at))"
    return 0
  fi

  printf '%d validation phase(s) failed in %ds; see the diagnostics above.\n' \
    "$failures" "$((SECONDS - started_at))" >&2
  return 1
}

cd "$REPO_ROOT" || exit 1
main "$@"
