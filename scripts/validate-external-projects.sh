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
readonly BUILD_FILES_PER_BATCH="${LEANFMT_VALIDATION_BUILD_BATCH_SIZE:-$VALIDATION_FILES_PER_BATCH}"
readonly FORMATTER_WORKER_BATCH_SIZE="${LEANFMT_VALIDATION_FORMATTER_BATCH_SIZE:-}"
readonly FORMATTER_ENV_CACHE_SIZE="${LEANFMT_VALIDATION_FORMATTER_ENV_CACHE_SIZE:-0}"
readonly FORMATTER_IMPORT_ENV_FIRST="${LEANFMT_VALIDATION_IMPORT_ENV_FIRST:-1}"
readonly FORMATTER_LINE_WIDTH="${LEANFMT_VALIDATION_LINE_WIDTH:-}"
readonly DEFAULT_FILE_SELECTOR="${LEANFMT_VALIDATION_FILE_PATTERN:-*.lean}"
readonly CSLIB_URL="https://github.com/leanprover/cslib.git"
readonly MATHLIB_URL="https://github.com/leanprover-community/mathlib4.git"

declare -a DEFAULT_PROJECTS=(
  "cslib|$CSLIB_URL|$DEFAULT_FILE_SELECTOR"
  "mathlib|$MATHLIB_URL|$DEFAULT_FILE_SELECTOR"
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

validate_nonnegative_integer() {
  local name="$1"
  local value="$2"

  if [[ "$value" =~ ^[0-9]+$ ]]; then
    return 0
  fi

  printf '%s must be a nonnegative integer, got %q.\n' "$name" "$value" >&2
  return 2
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

path_to_module_target() {
  local project_dir="$1"
  local path="$2"
  local relative="${path#"$project_dir/"}"

  case "$relative" in
    lakefile.lean)
      return 1
      ;;
  esac

  relative="${relative%.lean}"
  printf '%s\n' "${relative//\//.}"
}

build_selected_modules() {
  local project_dir="$1"
  local file_selector="$2"
  local -a targets=()
  local file
  local target

  while IFS= read -r -d '' file; do
    if target="$(path_to_module_target "$project_dir" "$file")"; then
      targets+=("$target")
    fi
  done < <(tracked_lean_files "$project_dir" "$file_selector")

  if ((${#targets[@]} == 0)); then
    printf 'No files matched %q in %s.\n' "$file_selector" "$project_dir"
    return 0
  fi

  (
    cd "$project_dir" || exit 1
    printf '%s\0' "${targets[@]}" |
      xargs -0 -n "$BUILD_FILES_PER_BATCH" lake build
  )
}

build_module_file_list() {
  local project_dir="$1"
  local list_file="$2"
  local -a targets=()
  local file
  local target

  while IFS= read -r -d '' file; do
    if target="$(path_to_module_target "$project_dir" "$file")"; then
      targets+=("$target")
    fi
  done < "$list_file"

  if ((${#targets[@]} == 0)); then
    printf 'No files listed for selected build in %s.\n' "$project_dir"
    return 0
  fi

  (
    cd "$project_dir" || exit 1
    printf '%s\0' "${targets[@]}" |
      xargs -0 -n "$BUILD_FILES_PER_BATCH" lake build
  )
}

build_project_or_selected_modules() {
  local project_dir="$1"
  local file_selector="$2"
  local selected_file_list="${3:-}"

  if [[ -n "$selected_file_list" ]]; then
    build_module_file_list "$project_dir" "$selected_file_list"
    return $?
  fi

  if [[ "$file_selector" == "$DEFAULT_FILE_SELECTOR" ]]; then
    build_project "$project_dir"
  else
    build_selected_modules "$project_dir" "$file_selector"
  fi
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

  local -a formatter_options=(--env-cache-size "$FORMATTER_ENV_CACHE_SIZE")
  if [[ "$FORMATTER_IMPORT_ENV_FIRST" == "1" ]]; then
    formatter_options+=(--import-env-first)
  fi
  if [[ -n "$FORMATTER_LINE_WIDTH" ]]; then
    formatter_options+=(--line-width "$FORMATTER_LINE_WIDTH")
  fi
  if [[ -n "$FORMATTER_WORKER_BATCH_SIZE" ]]; then
    formatter_options+=(--worker-batch-size "$FORMATTER_WORKER_BATCH_SIZE")
  fi

  (
    cd "$project_dir" || exit 1
    xargs -0 lake env "$FORMATTER" "${formatter_options[@]}" "$@" < "$list_file"
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

  local batch first_index count last_index list_file status
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

    if run_phase_result \
        "Build $project_name before formatting batch $batch/$total_batches ($file_selector)" \
        build_project_or_selected_modules "$project_dir" "$file_selector" \
          "$list_file"; then
      :
    else
      status=$?
      rm -f "$list_file"
      printf 'Stopping at validation batch %d/%d after pre-format build failed.\n' \
        "$batch" "$total_batches" >&2
      return "$status"
    fi

    if run_phase_result \
        "Check $project_name formatting exceptions/idempotence batch $batch/$total_batches ($file_selector)" \
        run_formatter_file_list "$project_dir" "$list_file" --check \
          --check-exception --check-idempotent; then
      :
    else
      status=$?
      rm -f "$list_file"
      printf 'Stopping at validation batch %d/%d after formatter diagnostics failed.\n' \
        "$batch" "$total_batches" >&2
      return "$status"
    fi

    if run_phase_result \
        "Format $project_name batch $batch/$total_batches after clean diagnostics ($file_selector)" \
        run_formatter_file_list "$project_dir" "$list_file" --check-exception \
          --check-idempotent; then
      :
    else
      status=$?
      rm -f "$list_file"
      printf 'Stopping at validation batch %d/%d after formatting failed.\n' \
        "$batch" "$total_batches" >&2
      return "$status"
    fi

    run_phase_result \
      "Build $project_name after formatting batch $batch/$total_batches ($file_selector)" \
      build_project_or_selected_modules "$project_dir" "$file_selector" \
        "$list_file"
    status=$?
    rm -f "$list_file"
    if ((status != 0)); then
      printf 'Stopping at validation batch %d/%d after post-format build failed.\n' \
        "$batch" "$total_batches" >&2
      return "$status"
    fi
  done

  return 0
}

selected_batch_file_list() {
  local project_dir="$1"
  local file_selector="$2"
  local selected_batch="$3"
  local output_file="$4"
  local -a files=()
  local file

  while IFS= read -r -d '' file; do
    files+=("$file")
  done < <(collect_tracked_lean_files "$project_dir" "$file_selector")

  if ((${#files[@]} == 0)); then
    : > "$output_file"
    return 0
  fi

  local total_files="${#files[@]}"
  local total_batches=$(((total_files + VALIDATION_FILES_PER_BATCH - 1) / VALIDATION_FILES_PER_BATCH))
  if ((selected_batch < 1 || selected_batch > total_batches)); then
    printf 'Batch %d is out of range for %s (%d file(s), %d batch(es)).\n' \
      "$selected_batch" "$file_selector" "$total_files" "$total_batches" >&2
    return 2
  fi

  local first_index=$(((selected_batch - 1) * VALIDATION_FILES_PER_BATCH))
  local count="$VALIDATION_FILES_PER_BATCH"
  if ((first_index + count > total_files)); then
    count=$((total_files - first_index))
  fi
  write_file_batch "$output_file" "$first_index" "$count" "${files[@]}"
}

main() {
  local started_at=$SECONDS
  local -a projects=("${DEFAULT_PROJECTS[@]}")
  local default_file_selector="$DEFAULT_FILE_SELECTOR"
  local selected_batch=""

  validate_positive_integer LEANFMT_VALIDATION_BATCH_SIZE \
    "$VALIDATION_FILES_PER_BATCH" || return $?
  validate_positive_integer LEANFMT_VALIDATION_BUILD_BATCH_SIZE \
    "$BUILD_FILES_PER_BATCH" || return $?
  if [[ -n "$FORMATTER_WORKER_BATCH_SIZE" ]]; then
    validate_positive_integer LEANFMT_VALIDATION_FORMATTER_BATCH_SIZE \
      "$FORMATTER_WORKER_BATCH_SIZE" || return $?
  fi
  validate_nonnegative_integer LEANFMT_VALIDATION_FORMATTER_ENV_CACHE_SIZE \
    "$FORMATTER_ENV_CACHE_SIZE" || return $?
  validate_boolean LEANFMT_VALIDATION_IMPORT_ENV_FIRST \
    "$FORMATTER_IMPORT_ENV_FIRST" || return $?
  if [[ -n "$FORMATTER_LINE_WIDTH" ]]; then
    validate_positive_integer LEANFMT_VALIDATION_LINE_WIDTH \
      "$FORMATTER_LINE_WIDTH" || return $?
  fi

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
        default_file_selector="$1"
        shift
        continue
      fi
      if [[ "$specification" == "--batch" ]]; then
        if (($# == 0)); then
          printf 'Missing value for --batch.\n' >&2
          return 2
        fi
        validate_positive_integer "--batch" "$1" || return $?
        selected_batch="$1"
        shift
        continue
      fi
      if [[ "$specification" != *=* ]]; then
        printf 'Invalid project %q; expected NAME=GIT_URL_OR_PATH[::FILE_SELECTOR].\n' \
          "$specification" >&2
        return 2
      fi
      local project_spec="${specification%%::*}"
      local file_selector="$default_file_selector"
      if [[ "$specification" == *"::"* ]]; then
        file_selector="${specification#*::}"
      fi
      projects+=("${project_spec%%=*}|${project_spec#*=}|$file_selector")
    done
    if ((${#projects[@]} == 0)); then
      projects=(
        "cslib|$CSLIB_URL|$default_file_selector"
        "mathlib|$MATHLIB_URL|$default_file_selector"
      )
    fi
  fi

  mkdir -p "$WORK_DIR"

  run_phase "Build leanfmt" lake build fmt
  if [[ ! -x "$FORMATTER" ]]; then
    printf 'Cannot continue without the formatter executable: %s\n' "$FORMATTER" >&2
    exit 1
  fi

  local project name url file_selector project_dir
  for project in "${projects[@]}"; do
    IFS='|' read -r name url file_selector <<< "$project"
    project_dir="$WORK_DIR/$name"

    run_phase "Clone $name" clone_project "$url" "$project_dir"
    if [[ ! -d "$project_dir/.git" ]]; then
      printf 'Skipping %s because its clone is unavailable.\n' "$name" >&2
      continue
    fi

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
