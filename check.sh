#!/bin/bash
set -e
ARGS=("$@")
ALLBINS=(ling ling-fmt)
export PATH=$PWD/tools:$PATH
one(){
  local title="$1"
  shift
  echo "== $title =="
  if cmdcheck "${ARGS[@]}" "$@"; then
    :
  else
    echo "Failed at $title, test suite aborted."
    exit 1
  fi
}
all(){
  for d in tests/* issues/*; do
    if [ "$d" != issues/keep.t ]; then
      if [ -z "$(ls "$d"/*-title)" ]; then
        echo "Missing DD-title file for directory $d"
        exit 1
      fi
    fi
  done
  for t in $(ls -d1 tests/*/*-title issues/*/*-title | sort -t / -k 3); do
    one "$(cat "$t")" "$(dirname "$t")"/*.t
  done
}

if ling --no-check --no-prims </dev/null >/dev/null; then
  :
else
  echo "The ling command is not in \$PATH"
  exit 1
fi

all

case "$AUTO" in
  (1|yes|true)
    ALLFULLBINS=()
    for b in "${ALLBINS[@]}"; do
      ALLFULLBINS=("${ALLFULLBINS}" "$(which "$b")")
    done
    while : ; do
      inotifywait -e delete "${ALLFULLBINS[@]}" || :
      all
    done;;
esac
