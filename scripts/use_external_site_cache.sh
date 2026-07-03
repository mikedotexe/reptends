#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
site_dir="$repo_root/site"
cache_parent="${QRT_SITE_CACHE_ROOT:-${XDG_CACHE_HOME:-$HOME/.cache}/quadratic-residue-reptends/site}"

move_or_link() {
  local name="$1"
  local source_path="$site_dir/$name"
  local target_path="$cache_parent/$name"

  mkdir -p "$(dirname "$target_path")"

  if [ -L "$source_path" ]; then
    local current_target
    current_target="$(readlink "$source_path")"
    if [ "$current_target" = "$target_path" ]; then
      echo "site/$name already points to $target_path"
      return 0
    fi
    echo "site/$name is already a symlink to $current_target" >&2
    echo "Remove it first if you want to retarget it to $target_path." >&2
    return 1
  fi

  if [ -d "$source_path" ]; then
    if [ -e "$target_path" ]; then
      echo "Cache target already exists: $target_path" >&2
      echo "Move or remove one side before retrying." >&2
      return 1
    fi
    mv "$source_path" "$target_path"
  elif [ -e "$source_path" ]; then
    echo "site/$name exists but is not a directory or symlink." >&2
    return 1
  else
    mkdir -p "$target_path"
  fi

  ln -s "$target_path" "$source_path"
  echo "site/$name -> $target_path"
}

mkdir -p "$cache_parent"
move_or_link node_modules
move_or_link dist
move_or_link .vite
