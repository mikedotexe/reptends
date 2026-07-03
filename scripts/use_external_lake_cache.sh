#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
lean_dir="$repo_root/lean"
lake_path="$lean_dir/.lake"
cache_parent="${QRT_LAKE_CACHE_ROOT:-${XDG_CACHE_HOME:-$HOME/.cache}/quadratic-residue-reptends/lean}"
cache_dir="$cache_parent/.lake"

mkdir -p "$cache_parent"

if [ -L "$lake_path" ]; then
  current_target="$(readlink "$lake_path")"
  if [ "$current_target" = "$cache_dir" ]; then
    echo "lean/.lake already points to $cache_dir"
    exit 0
  fi
  echo "lean/.lake is already a symlink to $current_target" >&2
  echo "Remove it first if you want to retarget it to $cache_dir." >&2
  exit 1
fi

if [ -d "$lake_path" ]; then
  if [ -e "$cache_dir" ]; then
    echo "Cache target already exists: $cache_dir" >&2
    echo "Move or remove one side before retrying." >&2
    exit 1
  fi
  mv "$lake_path" "$cache_dir"
elif [ -e "$lake_path" ]; then
  echo "lean/.lake exists but is not a directory or symlink." >&2
  exit 1
else
  mkdir -p "$cache_dir"
fi

ln -s "$cache_dir" "$lake_path"
echo "lean/.lake -> $cache_dir"
