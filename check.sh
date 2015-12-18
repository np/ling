#!/bin/sh
set -e
echo "== EXPECTED FAILURES =="
cmdcheck "$@" tests/failure/*.t
echo "== EXPECTED SUCCESSES =="
cmdcheck "$@" tests/success/*.t
echo "== EXPECTED SEQUENCE =="
cmdcheck "$@" tests/sequence/*.t
echo "== EXPECTED FUSION =="
cmdcheck "$@" tests/fusion/*.t
echo "== EXPECTED COMPILATION =="
cmdcheck "$@" tests/compile/*.t
echo "== EXPECTED NORMALIZED =="
cmdcheck "$@" tests/norm/*.t
echo "== EXPECTED PRETTY-PRINTER =="
cmdcheck "$@" tests/pretty/*.t
echo "== EXPECTED FMT =="
cmdcheck "$@" tests/fmt/*.t
echo "== EXPECTED STRICT-PAR FAILURES =="
cmdcheck "$@" tests/strict-par-failure/*.t
echo "== ISSUES CHECK =="
cmdcheck "$@" issues/check/*.t
echo "== ISSUES COMPILATION =="
cmdcheck "$@" issues/compile/*.t
