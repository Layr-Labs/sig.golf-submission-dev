#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
export PATH="${HOME}/.elan/bin:${PATH}"
git submodule update --init --recursive
python3 .contract/verifier/pin_contract.py check --root .contract
bash .contract/verifier/setup_tools.sh
cd .contract/formal
lake exe cache get
lake build OptimalOTS
