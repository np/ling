#!/bin/sh
set -e
echo MiniC; bnfc -d MiniC.cf
echo Ling; bnfc -d Ling.cf
echo Ling.Fmt.Albert; bnfc -p Ling.Fmt -d Ling/Fmt/Albert.cf
echo Ling.Fmt.Benjamin; bnfc -p Ling.Fmt -d Ling/Fmt/Benjamin.cf
git ls-files -z '*.hs' '*.y' | \
  grep -vzZ '/Test.hs$' | \
  xargs -0 -n 1 -- \
  sed -i -e 's/ \+$//' \
         -e '$ { /^$/ d}' \
         -e 's/^\Z//' \
         -e 's/^layoutSep   = ";"$/layoutSep   = ","/' \
         -e 's/^import\(  *\)\(Ling\..*\|MiniC\)\.ErrM$/import\1Ling.ErrM/'
rm -f MiniC/ErrM.hs Ling/Fmt/*/ErrM.hs \
      MiniC/Test.hs Ling/Test.hs Ling/Fmt/*/Test.hs
