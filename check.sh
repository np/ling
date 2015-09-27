#!/bin/sh
echo "== EXPECTED FAILURES =="
cmdcheck tests/failure/*.t
echo "== EXPECTED SUCCESSES =="
cmdcheck tests/success/*.t
echo "== EXPECTED COMPILATION =="
cmdcheck tests/compile/*.t
echo "== EXPECTED PRETTY-PRINTER =="
cmdcheck tests/pretty/*.t
echo "== EXPECTED FMT =="
cmdcheck tests/fmt/*.t
echo "== ISSUES CHECK =="
cmdcheck issues/check/*.t
echo "== ISSUES COMPILATION =="
cmdcheck issues/compile/*.t
