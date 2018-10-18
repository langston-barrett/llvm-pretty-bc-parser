((haskell-mode
  . ((dante-repl-command-line . ("nix-shell" "nix/shell.nix" "--pure" "--run" "cabal repl lib:llvm-pretty-bc-parser --builddir=dist/dante")))))
