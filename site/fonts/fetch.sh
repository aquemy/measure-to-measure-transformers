#!/usr/bin/env sh
# Fetch JuliaMono, the monospace font used for the Lean code listings in the PDF blueprint (it covers
# the Lean unicode: ⟪ ⟫ ‖ ⊥ ₊ ² 𝕊 ...). Idempotent; run before `quarto render site/blueprint.qmd`.
set -e
dir="$(cd "$(dirname "$0")" && pwd)"
base="https://github.com/cormullion/juliamono/raw/master"
for w in Regular Bold; do
  f="$dir/JuliaMono-$w.ttf"
  if [ ! -f "$f" ]; then
    echo "fetching JuliaMono-$w.ttf"
    curl -fsSL -o "$f" "$base/JuliaMono-$w.ttf"
  fi
done
echo "JuliaMono present in $dir"
