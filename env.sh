cmdr() {
  local args="$1"
  shift
  local dir="$1"
  shift
  for i; do
    i="${i%.ll}"
    cmdrecord tests/"$dir/$i".t --no-stdin --source "$i".ll --env empty -- Ling $args "$i".ll
    mv "$i".ll fixtures/all/
    ln -s ../all/"$i".ll fixtures/"$dir"/
    git add fixtures/all/"$i".ll fixtures/"$dir/$i".ll tests/"$dir/$i".t
  done
}
cmdrsuccess(){
  cmdr --check success "$@"
}
cmdrfailure(){
  cmdr --check failure "$@"
}
alias cmdrseq='cmdrecord tests/sequence/all.t --env empty -- Ling --seq < fixtures/sequence/*.ll'
alias cmdrcom='cmdrecord tests/compile/all.t  --env empty -- Ling --compile-prims --compile < fixtures/compile/*.ll'
alias cmdrfmt='cmdrecord tests/fmt/all.t  --env empty -- ling-fmt < fixtures/all/*.ll'
alias cmdrpretty='cmdrecord tests/pretty/all.t  --env empty -- Ling --pretty < fixtures/all/*.ll'
current_nixpkgs=$HOME/hub/np/nixpkgs
[ ! -d "$current_nixpkgs" ] || export NIX_PATH=nixpkgs=$current_nixpkgs
export PATH=`pwd`/dist/build/Ling:`pwd`/dist/build/ling-fmt:`pwd`/env/bin:$PATH
