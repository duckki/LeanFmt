#!/usr/bin/env bash

set -u
set -o pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)" || exit 1
readonly SCRIPT_DIR
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)" || exit 1
readonly REPO_ROOT
readonly FORMATTER="$REPO_ROOT/.lake/build/bin/fmt"
readonly WORK_DIR="${LEANFMT_VALIDATION_DIR:-$REPO_ROOT/.scratch/external-validation}"
readonly VALIDATION_FILES_PER_BATCH="${LEANFMT_VALIDATION_BATCH_SIZE:-100}"
readonly FORMATTER_WORKER_BATCH_SIZE="${LEANFMT_VALIDATION_FORMATTER_BATCH_SIZE:-}"
readonly FORMATTER_LINE_WIDTH="${LEANFMT_VALIDATION_LINE_WIDTH:-}"
readonly DEFAULT_FILE_SELECTOR="${LEANFMT_VALIDATION_FILE_PATTERN:-*.lean}"

failures=0

usage() {
  cat >&2 <<'EOF'
Usage:
  scripts/validate-external-projects.sh [--files FILE_SELECTOR] [--batch N] GIT_REPO[::FILE_SELECTOR]...
  scripts/validate-external-projects.sh [--files FILE_SELECTOR] [--batch N] NAME=GIT_REPO[::FILE_SELECTOR]...

Each project argument must name an explicit git clone source. The validator
creates a fresh clone under .scratch/external-validation/ before formatting.

Set LEANFMT_VALIDATION_LINE_WIDTH=N to pass --line-width N to every formatter
invocation. For example, validate mathlib at width 100 with:

  LEANFMT_VALIDATION_LINE_WIDTH=100 scripts/validate-external-projects.sh \
    --files Mathlib mathlib=$HOME/work/lean-libs/mathlib4
EOF
}

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

validate_positive_integer() {
  local name="$1"
  local value="$2"

  if [[ "$value" =~ ^[1-9][0-9]*$ ]]; then
    return 0
  fi

  printf '%s must be a positive integer, got %q.\n' "$name" "$value" >&2
  return 2
}

validate_boolean() {
  local name="$1"
  local value="$2"

  if [[ "$value" == "0" || "$value" == "1" ]]; then
    return 0
  fi

  printf '%s must be 0 or 1, got %q.\n' "$name" "$value" >&2
  return 2
}

clone_project() {
  local source="$1"
  local destination="$2"

  rm -rf "$destination"
  git clone "$source" "$destination"
}

absolute_path() {
  local path="$1"

  if [[ "$path" == /* ]]; then
    printf '%s\n' "$path"
  else
    printf '%s/%s\n' "$PWD" "$path"
  fi
}

project_name_from_path() {
  local path="$1"
  local name

  name="$(basename "$path")"
  name="${name%.git}"
  printf '%s\n' "$name"
}

validate_local_git_repo() {
  local path="$1"

  if [[ ! -d "$path" ]]; then
    printf 'Project path does not exist or is not a directory: %s\n' "$path" >&2
    return 2
  fi
  if ! git -C "$path" rev-parse --is-inside-work-tree >/dev/null 2>&1; then
    printf 'Project path is not a git repository: %s\n' "$path" >&2
    return 2
  fi
}

normalize_project_source() {
  local source="$1"

  if [[ -d "$source" ]]; then
    absolute_path "$source"
  else
    printf '%s\n' "$source"
  fi
}

validate_project_source() {
  local source="$1"

  if [[ -d "$source" ]]; then
    validate_local_git_repo "$source"
  fi
}

seed_local_lake_packages() {
  local source="$1"
  local destination="$2"

  if [[ -d "$source/.lake/packages" ]]; then
    mkdir -p "$destination/.lake"
    rm -rf "$destination/.lake/packages"
    cp -R "$source/.lake/packages" "$destination/.lake/"
  fi
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

tracked_lean_files() {
  local project_dir="$1"
  local file_selector="$2"
  local file

  if [[ -d "$project_dir/$file_selector" ]]; then
    while IFS= read -r -d '' file; do
      if [[ "$file" == *.lean ]]; then
        printf '%s\0' "$project_dir/$file"
      fi
    done < <(git -C "$project_dir" ls-files -z -- "$file_selector")
  else
    while IFS= read -r -d '' file; do
      printf '%s\0' "$project_dir/$file"
    done < <(git -C "$project_dir" ls-files -z -- "$file_selector")
  fi
}

collect_tracked_lean_files() {
  local project_dir="$1"
  local file_selector="$2"
  local file

  while IFS= read -r -d '' file; do
    printf '%s\0' "$file"
  done < <(tracked_lean_files "$project_dir" "$file_selector")
}

write_file_batch() {
  local output_file="$1"
  local first_index="$2"
  local count="$3"
  shift 3
  local -a files_ref=("$@")
  local index

  : > "$output_file"
  for ((index = first_index; index < first_index + count; index++)); do
    printf '%s\0' "${files_ref[$index]}" >> "$output_file"
  done
}

run_formatter_file_list() {
  local project_dir="$1"
  local list_file="$2"
  shift 2

  local -a formatter_command=(lake env "$FORMATTER")
  if [[ -n "$FORMATTER_LINE_WIDTH" ]]; then
    formatter_command+=(--line-width "$FORMATTER_LINE_WIDTH")
  fi
  if [[ -n "$FORMATTER_WORKER_BATCH_SIZE" ]]; then
    formatter_command+=(--worker-batch-size "$FORMATTER_WORKER_BATCH_SIZE")
  fi

  (
    cd "$project_dir" || exit 1
    xargs -0 "${formatter_command[@]}" "$@" < "$list_file"
  )
}

run_project_validation_batches() {
  local project_name="$1"
  local project_dir="$2"
  local file_selector="$3"
  local selected_batch="$4"
  local -a files=()
  local file

  while IFS= read -r -d '' file; do
    files+=("$file")
  done < <(collect_tracked_lean_files "$project_dir" "$file_selector")

  if ((${#files[@]} == 0)); then
    printf 'No files matched %q in %s.\n' "$file_selector" "$project_dir"
    return 0
  fi

  local total_files="${#files[@]}"
  local total_batches=$(((total_files + VALIDATION_FILES_PER_BATCH - 1) / VALIDATION_FILES_PER_BATCH))
  local first_batch=1
  local last_batch="$total_batches"

  if [[ -n "$selected_batch" ]]; then
    if ((selected_batch < 1 || selected_batch > total_batches)); then
      printf 'Batch %d is out of range for %s (%d file(s), %d batch(es)).\n' \
        "$selected_batch" "$file_selector" "$total_files" "$total_batches" >&2
      return 2
    fi
    first_batch="$selected_batch"
    last_batch="$selected_batch"
  fi

  printf 'Formatter file set: %s\n' "$file_selector"
  printf 'Total Lean files: %d\n' "$total_files"
  printf 'Validation batch size: %d file(s); total batches: %d\n' \
    "$VALIDATION_FILES_PER_BATCH" "$total_batches"
  if [[ -n "$FORMATTER_WORKER_BATCH_SIZE" ]]; then
    printf 'Formatter worker batch override: %d file(s)\n' \
      "$FORMATTER_WORKER_BATCH_SIZE"
  else
    printf 'Formatter worker batch override: auto\n'
  fi
  if [[ -n "$selected_batch" ]]; then
    printf 'Running selected validation batch: %d\n' "$selected_batch"
  fi

  local batch first_index count last_index list_file formatter_status build_status status

  if run_phase_result \
      "Build all of $project_name before formatting ($file_selector)" \
      build_project "$project_dir"; then
    :
  else
    status=$?
    printf 'Stopping before formatter batches after the initial build failed.\n' >&2
    return "$status"
  fi

  for ((batch = first_batch; batch <= last_batch; batch++)); do
    first_index=$(((batch - 1) * VALIDATION_FILES_PER_BATCH))
    count="$VALIDATION_FILES_PER_BATCH"
    if ((first_index + count > total_files)); then
      count=$((total_files - first_index))
    fi
    last_index=$((first_index + count - 1))

    list_file="$(mktemp "$WORK_DIR/$project_name-batch-$batch.XXXXXX")" || return 1
    write_file_batch "$list_file" "$first_index" "$count" "${files[@]}"

    printf '\n-- Formatter batch %d/%d: %d file(s), indexes %d-%d --\n' \
      "$batch" "$total_batches" "$count" "$((first_index + 1))" \
      "$((last_index + 1))"
    printf 'First file: %s\n' "${files[$first_index]#"$project_dir/"}"
    printf 'Last file:  %s\n' "${files[$last_index]#"$project_dir/"}"

    formatter_status=0
    if run_phase_result \
        "Format and check $project_name batch $batch/$total_batches ($file_selector)" \
        run_formatter_file_list "$project_dir" "$list_file" \
          --check-exception --check-idempotent; then
      :
    else
      formatter_status=$?
    fi

    if ((formatter_status == 130 || formatter_status == 143)); then
      rm -f "$list_file"
      printf 'Stopping at validation batch %d/%d after formatter interruption.\n' \
        "$batch" "$total_batches" >&2
      return "$formatter_status"
    fi

    build_status=0
    if run_phase_result \
        "Build all of $project_name after formatting batch $batch/$total_batches ($file_selector)" \
        build_project "$project_dir"; then
      :
    else
      build_status=$?
    fi

    rm -f "$list_file"
    if ((formatter_status != 0 || build_status != 0)); then
      printf 'Stopping at validation batch %d/%d after reporting formatter and build results.\n' \
        "$batch" "$total_batches" >&2
      if ((formatter_status != 0)); then
        return "$formatter_status"
      fi
      return "$build_status"
    fi
  done

  return 0
}

main() {
  local started_at=$SECONDS
  local -a projects=()
  local default_file_selector="$DEFAULT_FILE_SELECTOR"
  local selected_batch=""

  validate_positive_integer LEANFMT_VALIDATION_BATCH_SIZE \
    "$VALIDATION_FILES_PER_BATCH" || return $?
  if [[ -n "$FORMATTER_WORKER_BATCH_SIZE" ]]; then
    validate_positive_integer LEANFMT_VALIDATION_FORMATTER_BATCH_SIZE \
      "$FORMATTER_WORKER_BATCH_SIZE" || return $?
  fi
  if [[ -n "$FORMATTER_LINE_WIDTH" ]]; then
    validate_positive_integer LEANFMT_VALIDATION_LINE_WIDTH \
      "$FORMATTER_LINE_WIDTH" || return $?
  fi

  local specification project_spec file_selector project_name project_source
  while (($# > 0)); do
    specification="$1"
    shift
    if [[ "$specification" == "--help" || "$specification" == "-h" ]]; then
      usage
      return 0
    fi
    if [[ "$specification" == "--files" ]]; then
      if (($# == 0)); then
        printf 'Missing value for --files.\n' >&2
        usage
        return 2
      fi
      default_file_selector="$1"
      shift
      continue
    fi
    if [[ "$specification" == "--batch" ]]; then
      if (($# == 0)); then
        printf 'Missing value for --batch.\n' >&2
        usage
        return 2
      fi
      validate_positive_integer "--batch" "$1" || return $?
      selected_batch="$1"
      shift
      continue
    fi

    project_spec="${specification%%::*}"
    file_selector="$default_file_selector"
    if [[ "$specification" == *"::"* ]]; then
      file_selector="${specification#*::}"
    fi

    if [[ "$project_spec" == *=* ]]; then
      project_name="${project_spec%%=*}"
      project_source="${project_spec#*=}"
      if [[ -z "$project_name" || -z "$project_source" ]]; then
        printf 'Invalid project %q; expected NAME=GIT_REPO.\n' \
          "$project_spec" >&2
        usage
        return 2
      fi
    else
      project_source="$project_spec"
      project_name="$(project_name_from_path "$project_source")"
    fi

    project_source="$(normalize_project_source "$project_source")"
    validate_project_source "$project_source" || return $?
    projects+=("$project_name|$project_source|$file_selector")
  done

  if ((${#projects[@]} == 0)); then
    printf 'Missing required git repository argument.\n' >&2
    usage
    return 2
  fi

  mkdir -p "$WORK_DIR"

  run_phase "Build leanfmt" lake build fmt
  if [[ ! -x "$FORMATTER" ]]; then
    printf 'Cannot continue without the formatter executable: %s\n' "$FORMATTER" >&2
    exit 1
  fi

  local project name source file_selector project_dir
  for project in "${projects[@]}"; do
    IFS='|' read -r name source file_selector <<< "$project"
    project_dir="$WORK_DIR/$name"

    run_phase "Clone $name" clone_project "$source" "$project_dir"
    if [[ ! -d "$project_dir/.git" ]]; then
      printf 'Skipping %s because its clone is unavailable.\n' "$name" >&2
      continue
    fi

    seed_local_lake_packages "$source" "$project_dir"

    run_optional_phase "Download $name build cache" get_build_cache "$project_dir"
    run_project_validation_batches "$name" "$project_dir" "$file_selector" \
      "$selected_batch"
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
