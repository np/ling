#!/bin/sh
set -e
#echo MiniC; bnfc -d MiniC.cf
#echo Ling;     bnfc -d Ling.cf
cabal build
