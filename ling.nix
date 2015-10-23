{ mkDerivation, alex, array, base, containers, ghci-pretty, happy
, lens, mtl, stdenv, template-haskell
}:
mkDerivation {
  pname = "ling";
  version = "0.1.0.0";
  src = ./.;
  isLibrary = false;
  isExecutable = true;
  executableHaskellDepends = [
    array base containers ghci-pretty lens mtl template-haskell
  ];
  executableToolDepends = [ alex happy ];
  license = stdenv.lib.licenses.bsd3;
}
