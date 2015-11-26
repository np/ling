{ mkDerivation, alex, array, base, containers, deepseq, directory
, doctest, filepath, happy, hspec, HUnit, mtl, pretty, process
, QuickCheck, stdenv, temporary
}:
mkDerivation {
  pname = "BNFC";
  version = "2.8";
  sha256 = "0d3zcxspxcpnifv3kqg8d6gp01wxybakcbw7jh69gqg8rzfmzgi1";
  isLibrary = true;
  isExecutable = true;
  libraryHaskellDepends = [ array base ];
  executableHaskellDepends = [
    array base containers deepseq directory filepath mtl pretty process
  ];
  executableToolDepends = [ alex happy ];
  testHaskellDepends = [
    array base containers deepseq directory doctest filepath hspec
    HUnit mtl pretty process QuickCheck temporary
  ];
  homepage = "http://bnfc.digitalgrammars.com/";
  description = "A compiler front-end generator";
  license = stdenv.lib.licenses.gpl2;
}
