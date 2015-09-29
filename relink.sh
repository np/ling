#!/bin/zsh

# error() @ https://gist.github.com/3736727 {{{
error(){
  local code="$1"
  shift
  echo "error: $@" >>/dev/stderr
  exit "$code"
}
# }}}

# Adapted from:
# link() @ https://gist.github.com/3181899 {{{1
# Example:
# cd ~/configs
# link .zshrc ~/.zshrc
# link .vimrc ~/.vimrc
link(){
  local dst="$1"
  local ldst="$1"
  local src="$2"
  case "$dst" in
    /*) : ;;
    *) ldst="$(realpath "$dst" --relative-to="$(dirname "$2")")";;
  esac
  if [ -L "$src" ]; then
    # Check if the link is already as expected.
    [ $(readlink "$src") != "$ldst" ] || return 0
    rm "$src"
  elif [ -e "$src" ]; then
    if [ -e "$dst" ]; then
      until cmp "$src" "$dst"; do
        vimdiff "$src" "$dst"
      done
      if cmp "$src" "$dst"; then
        if [ -L "$dst" ]; then
          rm "$dst"
          mv "$src" "$dst"
        else
          rm "$src"
        fi
      fi
    else
      echo "moving $src to $dst" >>/dev/stderr
      mv "$src" "$dst"
    fi
  elif [ ! -e "$dst" ]; then
    # if nothing exists we do nothing
    return 0
  fi
  echo "linking $dst" >>/dev/stderr
  ln -s "$ldst" "$src"
}
# }}}

for d in fixtures/*; do
  if [ "$d" != fixtures/all ]; then
    for f in "$d"/*.ll; do
      b="$(basename "$f")"
      link fixtures/all/"$b" "$f"
    done
  fi
done

for t in tests/**/*.t/*.ll issues/**/*.ll; do
  f=fixtures/all/"$(basename "$t")"
  if [ -e "$f" ]; then
    link "$f" "$t"
  else
    error 1 "Missing file $f"
  fi
done
