#!/usr/bin/env bash
# Launch the nixvim configuration with a LOCAL, patched checkout of cornelis
# instead of the pinned github:agda/cornelis input.
#
# The local checkout lives at ~/cornelis. Edit its Haskell sources there and
# re-run this script; nix rebuilds only the cornelis binary (and the tiny nvim
# wrapper) before launching.
#
# Why this is needed: cornelis' upstream release predates Agda 2.9.0's JSON
# interaction protocol. The `giveResult` object no longer always carries a
# "str" key (it may instead be {"paren": bool}), which made `:CornelisRefine`
# fail with `Error in $: key "str" not found`. The local checkout patches the
# GiveAction decoder to handle both shapes.
set -euo pipefail

FLAKE="${FLAKE:-$HOME/Dropbox/nixvim-flake}"
CORNELIS="${CORNELIS:-$HOME/cornelis}"

exec nix run "$FLAKE#default" \
  --override-input cornelis "path:$CORNELIS" \
  -- "$@"
