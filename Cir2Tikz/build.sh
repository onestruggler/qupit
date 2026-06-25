#!/usr/bin/env bash
# Regenerate all .tikz from the Haskell source, then build test3.pdf.
#   usage:  ./build.sh            # generate tikz + build test3.pdf
#           ./build.sh gen        # generate tikz only
# GHC is the Homebrew keg-only install (off the default PATH).
set -e
export PATH="$(brew --prefix ghc@9.12)/bin:$PATH"

echo ">> compiling main.hs"
ghc --make -O0 main.hs -o main_local

echo ">> running generator (writes *.tikz and chains/*.tikz)"
./main_local

if [ "${1:-}" != "gen" ]; then
  echo ">> pdflatex test3.tex (x2)"
  pdflatex -interaction=nonstopmode -halt-on-error test3.tex >/dev/null
  pdflatex -interaction=nonstopmode -halt-on-error test3.tex >/dev/null
  echo ">> wrote test3.pdf"
fi
