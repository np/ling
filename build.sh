#!/bin/sh
set -e
#echo MiniC; bnfc -d MiniC.cf
#echo Ling;     bnfc -d Ling.cf
# Past version for migration tool
#echo Ling.Fmt.Albert; bnfc -p Ling.Fmt -d Ling/Fmt/Albert.cf
cabal build
