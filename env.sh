cmdr() {
  local args=()
  while [ "$1" != -- ]; do
    args=("$1" "${args[@]}")
    shift
  done
  shift
  local dir="$1"
  shift
  for i; do
    mv "$i" fixtures/all/
    i="$(basename "$i")"
    i="${i%.ll}"
    pushd fixtures/all/
    mkdir -p ../../tests/"$dir"
    cmdrecord ../../tests/"$dir/$i".t --no-stdin --source "$i".ll --env empty -- Ling "${args[@]}" "$i".ll
    popd
    ln -s ../all/"$i".ll fixtures/"$dir"/
    rm tests/"$dir"/"$i".t/"$i".ll
    ln -s ../../../fixtures/all/"$i".ll tests/"$dir"/"$i".t/
    git add fixtures/all/"$i".ll fixtures/"$dir/$i".ll tests/"$dir/$i".t
  done
}
cmdrsuccess(){
  cmdr --check -- success "$@"
}
cmdrfailure(){
  cmdr --check -- failure "$@"
}
cmdrstrictparfailure(){
  cmdr --strict-par --check -- strict-par-failure "$@"
}
cmdrseq(){
  cmdr --seq -- sequence "$@"
}
cmdrcompile(){
  cmdr --compile -- compile "$@"
}
cmdrpretty(){
  cmdr --pretty -- pretty "$@"
}
cmdrnorm(){
  cmdr --norm -- norm "$@"
}
alias cmdrseqall='cmdrecord tests/sequence/all.t --env empty -- Ling --seq < fixtures/sequence/*.ll'
alias cmdrcompileall='cmdrecord tests/compile/all.t  --env empty -- Ling --compile-prims --compile < fixtures/compile/*.ll'
alias cmdrfmtall='cmdrecord tests/fmt/all.t  --env empty -- ling-fmt < fixtures/all/*.ll'
alias cmdrprettyall='cmdrecord tests/pretty/all.t  --env empty -- Ling --pretty < fixtures/all/*.ll'
alias cmdrnormall='cmdrecord tests/norm/all.t  --env empty -- Ling --norm < fixtures/success/*.ll'
alias cmdrstrictparsuccessall='cmdrecord tests/success/strict-par.t  --env empty -- Ling --strict-par --check  < fixtures/strict-par-success/*.ll'
# nixpkgs commit ef17efa99b0e644bbd2a28c0c3cfe5a2e57b21ea
current_nixpkgs=$HOME/hub/np/nixpkgs
[ ! -d "$current_nixpkgs" ] || export NIX_PATH=nixpkgs=$current_nixpkgs
DIST=`pwd`/dist
export PATH="$DIST"/build/Ling:"$DIST"/build/ling-fmt:"$DIST"/shims:$PATH

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
  # dst is the TARGET
  # src is the LINK_NAME
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

mkdir -p "$DIST"/shims

for i in \
  bnfc \
  cabal \
  gcc \
  ghc \
  ghci \
  ghc-make \
  ghc-mod \
  ghc-modi \
  ghc-pkg \
  hlint \
  stylish-haskell
do
  link 'run-in-nix-shell' "$DIST"/shims/"$i"
done
