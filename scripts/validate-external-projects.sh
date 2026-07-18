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
readonly DEFAULT_FILE_PATTERN="${LEANFMT_VALIDATION_FILE_PATTERN:-*.lean}"
readonly CSLIB_URL="https://github.com/leanprover/cslib.git"
readonly MATHLIB_URL="https://github.com/leanprover-community/mathlib4.git"

declare -a DEFAULT_PROJECTS=(
  "cslib|$CSLIB_URL|$DEFAULT_FILE_PATTERN"
  "mathlib|$MATHLIB_URL|$DEFAULT_FILE_PATTERN"
)

failures=0

section() {
  printf '\n==> %s\n' "$1"
}

run_phase_result() {
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
    return "$status"
  fi
}

run_phase() {
  run_phase_result "$@"
  return 0
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
  local file_pattern="$2"
  shift 2
  local -a files=()
  local file

  while IFS= read -r -d '' file; do
    files+=("$project_dir/$file")
  done < <(git -C "$project_dir" ls-files -z -- "$file_pattern")

  if ((${#files[@]} == 0)); then
    printf 'No files matched %q in %s.\n' "$file_pattern" "$project_dir"
    return 0
  fi

  (
    cd "$project_dir" || exit 1
    printf '%s\0' "${files[@]}" |
      xargs -0 -n "$FILES_PER_BATCH" lake env "$FORMATTER" "$@"
  )
}

main() {
  local started_at=$SECONDS
  local -a projects=("${DEFAULT_PROJECTS[@]}")
  local default_file_pattern="$DEFAULT_FILE_PATTERN"
  if (($# > 0)); then
    projects=()
    local specification
    while (($# > 0)); do
      specification="$1"
      shift
      if [[ "$specification" == "--files" ]]; then
        if (($# == 0)); then
          printf 'Missing value for --files.\n' >&2
          return 2
        fi
        default_file_pattern="$1"
        shift
        continue
      fi
      if [[ "$specification" != *=* ]]; then
        printf 'Invalid project %q; expected NAME=GIT_URL_OR_PATH[::GIT_PATHSPEC].\n' \
          "$specification" >&2
        return 2
      fi
      local project_spec="${specification%%::*}"
      local file_pattern="$default_file_pattern"
      if [[ "$specification" == *"::"* ]]; then
        file_pattern="${specification#*::}"
      fi
      projects+=("${project_spec%%=*}|${project_spec#*=}|$file_pattern")
    done
    if ((${#projects[@]} == 0)); then
      projects=(
        "cslib|$CSLIB_URL|$default_file_pattern"
        "mathlib|$MATHLIB_URL|$default_file_pattern"
      )
    fi
  fi

  mkdir -p "$WORK_DIR"

  run_phase "Build leanfmt" lake build fmt
  if [[ ! -x "$FORMATTER" ]]; then
    printf 'Cannot continue without the formatter executable: %s\n' "$FORMATTER" >&2
    exit 1
  fi

  local project name url file_pattern project_dir
  for project in "${projects[@]}"; do
    IFS='|' read -r name url file_pattern <<< "$project"
    project_dir="$WORK_DIR/$name"

    run_phase "Clone $name" clone_project "$url" "$project_dir"
    if [[ ! -d "$project_dir/.git" ]]; then
      printf 'Skipping %s because its clone is unavailable.\n' "$name" >&2
      continue
    fi

    run_optional_phase "Download $name build cache" get_build_cache "$project_dir"
    run_phase "Build $name before formatting" build_project "$project_dir"
    if run_phase_result "Check $name formatting exceptions/idempotence ($file_pattern)" \
        run_formatter "$project_dir" "$file_pattern" --check --check-exception \
          --check-idempotent; then
      if run_phase_result "Format $name after clean diagnostics ($file_pattern)" \
          run_formatter "$project_dir" "$file_pattern" --check-exception \
            --check-idempotent; then
        run_phase "Build $name after formatting" build_project "$project_dir"
      else
        printf 'Skipping post-format build for %s because formatting failed.\n' \
          "$name" >&2
      fi
    else
      printf 'Skipping formatter writes and post-format build for %s because diagnostics failed.\n' \
        "$name" >&2
    fi
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
