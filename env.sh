cmdr() {
  for i; do
    i="${i%.ll}"
    cmdrecord tests/$i.t --no-stdin --source $i.ll --env empty -- Lin --check $i.ll
    mv $i.ll fixtures/
    git add fixtures/$i.ll tests/$i.t
  done
}
export PATH=`pwd`/dist/build/Lin:$PATH
