#!/bin/zsh

. ./env.sh

cat fixtures/all/*.ll > fixtures/all.ll
cat fixtures/success/*.ll > fixtures/success.ll

for d in fixtures/*/; do
  if [ "$d" != fixtures/all/ ]; then
    for f in "$d"*.ll; do
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

link fixtures/all.ll tests/fmt/all.t/stdin
link fixtures/all.ll tests/pretty/all.t/stdin
link fixtures/success.ll tests/norm/all.t/stdin
link fixtures/success.ll tests/expand/all.t/stdin
link fixtures/success.ll tests/reduce/all.t/stdin
