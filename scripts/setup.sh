#!/usr/bin/env bash
set -euo pipefail
unset BENCHMARK_INSECURE_LOCAL
git submodule update --init --recursive
export PATH="$HOME/.elan/bin:$PATH"
if ! command -v elan >/dev/null 2>&1; then
  curl --proto '=https' --tlsv1.2 -sSfL \
    https://raw.githubusercontent.com/leanprover/elan/464c9d28395000a2a0128e07081e4956d50eced2/elan-init.sh \
    | sh -s -- -y --default-toolchain none
fi
toolchain="$(tr -d '[:space:]' < .contract/formal/lean-toolchain)"
elan toolchain install "$toolchain"
bash .contract/verifier/setup_tools.sh
