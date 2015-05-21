#!/bin/sh
echo "== EXPECTED FAILURES =="
cmdcheck tests/failure/*.t
echo "== EXPECTED SUCCESSES =="
cmdcheck tests/success/*.t
echo "== EXPECTED COMPILATION =="
cmdcheck tests/compile/*.t
echo "== ISSUES CHECK =="
cmdcheck issues/check/*.t
echo "== ISSUES COMPILATION =="
cmdcheck issues/compile/*.t
