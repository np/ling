{ mkDerivation, ansi-wl-pprint, base, Cabal, Diff, directory
, filepath, haskell-src-exts, hindent, hlint, HUnit
, optparse-applicative, pipes, pretty, stdenv, stylish-haskell
, test-framework, test-framework-hunit, text
}:
mkDerivation {
  pname = "hfmt";
  version = "0.0.1.0";
  sha256 = "07b6p35avs5rfy08kzvvfmigsvfn19gbvax7k5bi9h4h16yk1gbq";
  isLibrary = true;
  isExecutable = true;
  libraryHaskellDepends = [
    base Cabal Diff directory filepath haskell-src-exts hindent hlint
    HUnit pipes pretty stylish-haskell text
  ];
  executableHaskellDepends = [
    ansi-wl-pprint base Diff optparse-applicative pipes pretty
  ];
  testHaskellDepends = [
    base HUnit test-framework test-framework-hunit
  ];
  doCheck = false;
  homepage = "http://github.com/danstiner/hfmt";
  description = "Haskell source code formatter";
  license = stdenv.lib.licenses.mit;
}
