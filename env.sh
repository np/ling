cmdr() {
  local dir="$1"
  shift
  for i; do
    i="${i%.ll}"
    cmdrecord tests/"$dir/$i".t --no-stdin --source "$i".ll --env empty -- Lin --check "$i".ll
    mv "$i".ll fixtures/"$dir"
    git add fixtures/"$dir/$i".ll tests/"$dir/$i".t
  done
}
export PATH=`pwd`/dist/build/Lin:$PATH
