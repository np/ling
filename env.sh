cmdr() {
  local args="$1"
  shift
  local dir="$1"
  shift
  for i; do
    i="${i%.ll}"
    cmdrecord tests/"$dir/$i".t --no-stdin --source "$i".ll --env empty -- Lin $args "$i".ll
    mv "$i".ll fixtures/"$dir"
    git add fixtures/"$dir/$i".ll tests/"$dir/$i".t
  done
}
alias cmdrseq='cmdrecord tests/sequence/all.t --env empty -- Lin --seq < fixtures/sequence/*.ll'
export PATH=`pwd`/dist/build/Lin:$PATH
