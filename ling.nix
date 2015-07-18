{ mkDerivation, alex, array, base, containers, happy, lens, mtl
, stdenv
}:
mkDerivation {
  pname = "ling";
  version = "0.1.0.0";
  src = ./.;
  isLibrary = false;
  isExecutable = true;
  buildDepends = [ array base containers lens mtl ];
  buildTools = [ alex happy ];
  license = stdenv.lib.licenses.bsd3;
}
