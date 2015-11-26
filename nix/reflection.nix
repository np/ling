{ mkDerivation, base, stdenv, template-haskell }:
mkDerivation {
  pname = "reflection";
  version = "2.1";
  sha256 = "10w3m6v3g6am203wbrikdbp57x9vw6b4jsh7bxdzsss4nmpm81zg";
  libraryHaskellDepends = [ base template-haskell ];
  homepage = "http://github.com/ekmett/reflection";
  description = "Reifies arbitrary terms into types that can be reflected back into terms";
  license = stdenv.lib.licenses.bsd3;
}
