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
readonly FORMATTER_WORKER_JOBS="${LEANFMT_VALIDATION_FORMATTER_JOBS:-}"
readonly FORMATTER_LINE_WIDTH="${LEANFMT_VALIDATION_LINE_WIDTH:-}"
readonly DEFAULT_FILE_SELECTOR="${LEANFMT_VALIDATION_FILE_PATTERN:-*.lean}"

failures=0

usage() {
  cat >&2 <<'EOF'
Usage:
  scripts/validate-external-projects.sh [--files FILE_SELECTOR] [--batch N | --start-batch N] [--reuse-clone] [--skip-initial-build] [--skip-final-build] GIT_REPO[::FILE_SELECTOR]...
  scripts/validate-external-projects.sh [--files FILE_SELECTOR] [--batch N | --start-batch N] [--reuse-clone] [--skip-initial-build] [--skip-final-build] NAME=GIT_REPO[::FILE_SELECTOR]...

Each project argument must name an explicit git clone source. The validator
creates a fresh clone under .scratch/external-validation/ before formatting
unless --reuse-clone is passed.
Pass --skip-final-build to omit the complete build after every requested
formatter batch succeeds. A formatter failure never triggers a build.
The complete build before formatting still runs.
Pass --start-batch N to validate batch N and every later batch. Pass
--reuse-clone to keep an existing scratch clone, and --skip-initial-build to
omit its already-completed pre-format build while resuming validation.

Set LEANFMT_VALIDATION_LINE_WIDTH=N to pass --line-width N to every formatter
invocation. For example, validate mathlib at width 100 with:

  LEANFMT_VALIDATION_LINE_WIDTH=100 scripts/validate-external-projects.sh \
    --files Mathlib mathlib=$HOME/work/lean-libs/mathlib4

Set LEANFMT_VALIDATION_FORMATTER_JOBS=N to limit concurrent formatter workers.
Default-environment work uses the hardware count; the imported-environment
automatic default is capped at two.
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
  if [[ -n "$FORMATTER_WORKER_JOBS" ]]; then
    formatter_command+=(--jobs "$FORMATTER_WORKER_JOBS")
  fi

  (
    cd "$project_dir" || exit 1
    xargs -0 "${formatter_command[@]}" "$@" < "$list_file"
  )
}

run_logged_formatter_file_list() {
  local project_dir="$1"
  local list_file="$2"
  local log_file="$3"
  shift 3

  {
    printf 'Project directory: %s\n' "$project_dir"
    printf 'File list: %s\n' "$list_file"
    printf 'Formatter invocations: serial; formatter workers: concurrent\n'
    run_formatter_file_list "$project_dir" "$list_file" "$@"
  } 2>&1 | tee "$log_file"
}

run_project_validation_batches() {
  local project_name="$1"
  local project_dir="$2"
  local file_selector="$3"
  local selected_batch="$4"
  local start_batch="$5"
  local skip_initial_build="$6"
  local skip_final_build="$7"
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
  elif [[ -n "$start_batch" ]]; then
    if ((start_batch < 1 || start_batch > total_batches)); then
      printf 'Starting batch %d is out of range for %s (%d file(s), %d batch(es)).\n' \
        "$start_batch" "$file_selector" "$total_files" "$total_batches" >&2
      return 2
    fi
    first_batch="$start_batch"
  fi

  printf 'Formatter file set: %s\n' "$file_selector"
  printf 'Total Lean files: %d\n' "$total_files"
  printf 'Validation batch size: %d file(s); total batches: %d\n' \
    "$VALIDATION_FILES_PER_BATCH" "$total_batches"
  if [[ -n "$FORMATTER_WORKER_JOBS" ]]; then
    printf 'Formatter worker jobs override: %d\n' "$FORMATTER_WORKER_JOBS"
  else
    printf 'Formatter worker jobs override: automatic (hardware count; exact environments up to 2)\n'
  fi
  if [[ -n "$selected_batch" ]]; then
    printf 'Running selected validation batch: %d\n' "$selected_batch"
  elif [[ -n "$start_batch" ]]; then
    printf 'Starting validation at batch: %d\n' "$start_batch"
  fi

  local log_dir="$WORK_DIR/logs/$project_name"
  local state_file="$log_dir/state"
  local batch first_index count last_index list_file log_file
  local formatter_status build_status status

  mkdir -p "$log_dir"
  printf 'Formatter batch logs: %s\n' "$log_dir"

  if ((skip_initial_build == 1)); then
    section "Skip initial build of $project_name before formatting ($file_selector)"
    printf 'SKIPPED: initial build disabled by --skip-initial-build.\n'
  else
    if run_phase_result \
        "Build all of $project_name before formatting ($file_selector)" \
        build_project "$project_dir"; then
      :
    else
      status=$?
      printf 'Stopping before formatter batches after the initial build failed.\n' >&2
      return "$status"
    fi
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
    log_file="$log_dir/batch-$batch.log"

    printf '\n-- Formatter batch %d/%d: %d file(s), indexes %d-%d --\n' \
      "$batch" "$total_batches" "$count" "$((first_index + 1))" \
      "$((last_index + 1))"
    printf 'First file: %s\n' "${files[$first_index]#"$project_dir/"}"
    printf 'Last file:  %s\n' "${files[$last_index]#"$project_dir/"}"
    printf 'Batch log:  %s\n' "$log_file"
    printf 'batch=%d\nstatus=running\nlog=%s\n' \
      "$batch" "$log_file" > "$state_file"

    formatter_status=0
    if run_phase_result \
        "Format and check $project_name batch $batch/$total_batches ($file_selector)" \
        run_logged_formatter_file_list "$project_dir" "$list_file" "$log_file" \
          --check-exception --check-idempotent; then
      :
    else
      formatter_status=$?
    fi
    if ((formatter_status == 0)); then
      printf 'batch=%d\nstatus=passed\nlog=%s\n' \
        "$batch" "$log_file" > "$state_file"
    else
      printf 'batch=%d\nstatus=failed\nexit=%d\nlog=%s\n' \
        "$batch" "$formatter_status" "$log_file" > "$state_file"
    fi

    rm -f "$list_file"
    if ((formatter_status == 130 || formatter_status == 143)); then
      printf 'Stopping at validation batch %d/%d after formatter interruption.\n' \
        "$batch" "$total_batches" >&2
      return "$formatter_status"
    fi

    if ((formatter_status != 0)); then
      printf 'Stopping at validation batch %d/%d without a final build.\n' \
        "$batch" "$total_batches" >&2
      return "$formatter_status"
    fi
  done

  if ((skip_final_build == 1)); then
    section "Skip final build of $project_name after all requested formatter batches passed ($file_selector)"
    printf 'SKIPPED: final build disabled by --skip-final-build.\n'
    return 0
  fi

  build_status=0
  if run_phase_result \
      "Build all of $project_name after all requested formatter batches passed ($file_selector)" \
      build_project "$project_dir"; then
    :
  else
    build_status=$?
  fi

  if ((build_status != 0)); then
    printf 'Stopping after the final project build failed.\n' >&2
    return "$build_status"
  fi

  return 0
}

main() {
  local started_at=$SECONDS
  local -a projects=()
  local default_file_selector="$DEFAULT_FILE_SELECTOR"
  local selected_batch=""
  local start_batch=""
  local reuse_clone=0
  local skip_initial_build=0
  local skip_final_build=0

  validate_positive_integer LEANFMT_VALIDATION_BATCH_SIZE \
    "$VALIDATION_FILES_PER_BATCH" || return $?
  if [[ -n "$FORMATTER_WORKER_JOBS" ]]; then
    validate_positive_integer LEANFMT_VALIDATION_FORMATTER_JOBS \
      "$FORMATTER_WORKER_JOBS" || return $?
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
    if [[ "$specification" == "--start-batch" ]]; then
      if (($# == 0)); then
        printf 'Missing value for --start-batch.\n' >&2
        usage
        return 2
      fi
      validate_positive_integer "--start-batch" "$1" || return $?
      start_batch="$1"
      shift
      continue
    fi
    if [[ "$specification" == "--reuse-clone" ]]; then
      reuse_clone=1
      continue
    fi
    if [[ "$specification" == "--skip-initial-build" ]]; then
      skip_initial_build=1
      continue
    fi
    if [[ "$specification" == "--skip-final-build" ]]; then
      skip_final_build=1
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
  if [[ -n "$selected_batch" && -n "$start_batch" ]]; then
    printf '%s\n' '--batch and --start-batch cannot be used together.' >&2
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

    if ((reuse_clone == 1)); then
      run_phase "Reuse existing $name clone" validate_local_git_repo "$project_dir"
    else
      run_phase "Clone $name" clone_project "$source" "$project_dir"
    fi
    if [[ ! -d "$project_dir/.git" ]]; then
      printf 'Skipping %s because its clone is unavailable.\n' "$name" >&2
      continue
    fi

    if ((reuse_clone == 0)); then
      seed_local_lake_packages "$source" "$project_dir"
      run_optional_phase "Download $name build cache" get_build_cache "$project_dir"
    fi
    run_project_validation_batches "$name" "$project_dir" "$file_selector" \
      "$selected_batch" "$start_batch" "$skip_initial_build" "$skip_final_build"
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
