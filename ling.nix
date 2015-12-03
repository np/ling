{ mkDerivation, alex, array, base, containers, ghci-pretty, happy
, lens, mtl, SHA, stdenv, template-haskell
}:
mkDerivation {
  pname = "ling";
  version = "0.1.0.0";
  src = ./.;
  isLibrary = false;
  isExecutable = true;
  executableHaskellDepends = [
    array base containers ghci-pretty lens mtl SHA template-haskell
  ];
  executableToolDepends = [ alex happy ];
  license = stdenv.lib.licenses.bsd3;
}
