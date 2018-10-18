((haskell-mode
  . ((dante-repl-command-line . ("nix-shell" "nix/shell.nix" "--pure" "--run" "cd .. && cabal repl disasm-test --builddir=dist/dante")))))
