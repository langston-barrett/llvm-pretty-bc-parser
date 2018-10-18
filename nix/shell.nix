{ pkgs ? import ./pinned-pkgs.nix { } }:

let gpkgs = import ../../galois-haskell-nix/default.nix {
      compiler = "ghc843";
    };
    llvm-pretty-bc-parser = gpkgs.haskellPackages.llvm-pretty-bc-parser;
in with pkgs; stdenv.mkDerivation {
  name = "llvm-pretty-bc-parser";
  src = if lib.inNixShell then null else lib.sourceFilesBySuffices ../. [ ".cabal" ".hs" ];
  shellHook = ''
    export HOME=$(mktemp -d)
  '';
  buildInputs = [
    (gpkgs.haskellPackages.ghcWithHoogle (hpkgs: with hpkgs; [
      ghcid
      wl-pprint
    ] ++ llvm-pretty-bc-parser.buildInputs ++ llvm-pretty-bc-parser.propagatedBuildInputs))

    haskellPackages.cabal-install
    haskellPackages.doctest
    haskellPackages.hasktags
    haskellPackages.hindent
    haskellPackages.hlint
    haskellPackages.stylish-cabal

    clang
    zsh git which
  ];
}
