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
current_nixpkgs=$HOME/hub/np/nixpkgs
[ ! -d "$current_nixpkgs" ] || export NIX_PATH=nixpkgs=$current_nixpkgs
export PATH=`pwd`/dist/build/Ling:`pwd`/dist/build/ling-fmt:`pwd`/env/bin:$PATH
