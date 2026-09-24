# sig.golf on Yukon

Optimize a stateless hash-based signature scheme under the pinned
[beta rules](https://github.com/leanEthereum/sig.golf-dev/blob/05c5af7a7020e5104eb37b420dc87139f37f0e4b/README.md).
The single `full` track minimizes **signature bytes × RISC-V verification cycles**.
Yukon promotions are manual. The repository name `ots.golf` is historical; this
checkout contains the sig.golf beta benchmark.

## Baseline and contract

The starting proof comes from [upstream PR #19](https://github.com/leanEthereum/sig.golf-submissions/pull/19),
commit `7fdbf04354520ade6ea451d7f36871011bd4e144`. Its published verification used
contract `05c5af7a7020e5104eb37b420dc87139f37f0e4b`, which is the `.contract` submodule pin.
The recorded result is **119,632 bytes × 5,617,758 cycles = 672,063,625,056**.
`BASELINE.json` records the source and verification provenance. All admitted proof files
are copied unchanged; upstream presentation files are excluded by the source policy.
This is an upstream verification record, not a successful run of this Yukon workflow.

## Develop and submit

Only `submission/` is editable: `claim.json`, `Solution.lean` and the
`SigGolfCandidate/` Lean modules. The pinned verifier checks source policy,
claim matching, permitted axioms and the certificate. Read the pinned beta rules
for the exact model and proof obligations; the old main-branch hash-work contract
and its diagnostic flags do not apply here.

From the repository root on Linux:

```sh
bash scripts/setup.sh
python3 scripts/run.py
```

Setup installs elan through a pinned installer, selects the contract's Lean toolchain,
builds the verifier tools and trusted `SigGolf` library, and checks Linux prerequisites.
Go 1.24+, Landlock and user systemd with the verifier's required namespace and resource
isolation must be available. The verifier checks isolation before compiling a candidate.
Unsupported hosts fail; there is no unsandboxed scoring fallback.

After Yukon import, use `yukon setup --track full`, `yukon run --track full` and
`yukon submit --track full`. `yukon switch full` changes the selected track without
changing Git branches or files. CI evaluates the dispatched checkout; local runs
include working-tree edits. Failed verification emits no score. The wrapper preserves
exact integer scores and rejects any value beyond Yukon's safe integer range.

## Workflow and caches

The manual `benchmark.yml` workflow uses `blacksmith-16vcpu-ubuntu-2404` (64 GB RAM).
Because the Blacksmith host lacks Landlock, `scripts/blacksmith.sh` boots a checksum-pinned
Ubuntu 26.04 KVM guest with 12 vCPUs and 32 GB RAM. The verifier runs as an unprivileged
user under `/srv`, with Landlock and the upstream systemd isolation checks intact.
The job allows five hours around the verifier's four-hour, 24 GiB limit. The VM is stopped
on success or failure, and verifier logs and the guest console are retained as artifacts.

The guest's elan/toolchains, complete `.contract/.lake` dependency/build workspaces and
verifier tools are cached together by contract commit and bootstrap-script hashes.
Only the default branch saves shared caches, before candidate verification. Candidate
outputs and scores are never cached. Restored tools still run the upstream setup checks.

Yukon owns submission PRs and promotions. Do not enable the original upstream record
publisher on this repository. `records.json` is not updated by Yukon.

## License

See `LICENSE` and the pinned contract's `THIRD_PARTY_NOTICES.md` for upstream licensing.
