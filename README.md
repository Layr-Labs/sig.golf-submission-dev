# ots.golf on Yukon

Improve Lean-kernel-verified bounds on the worst-case verification cost of hash-based
one-time signatures. This repository contains five independent Yukon tracks on one branch.
The pinned `.contract` supplies the model and official verifier; `formal/Submissions/`
contains the editable proofs. `BASELINE.json` records the original proof sources and claims.

| Track | Editable folder under `formal/Submissions/` | Better score |
|---|---|---|
| `lower-generality-1` | `LowerGenerality1` | Higher compression bound |
| `lower-generality-2` | `LowerGenerality2` | Higher compression bound |
| `lower-generality-3` | `LowerGenerality3` | Higher compression bound |
| `upper-compressions` | `UpperCompressions` | Fewer compressions |
| `upper-riscv` | `UpperRiscv` | Fewer RISC-V cycles |

Read the mathematical statements, permitted imports, proof-root format, axiom restrictions
and resource limits in [.contract/AGENTS.md](.contract/AGENTS.md). This repository uses the
Yukon submission and promotion workflow below. The ots.golf website's separate PR intake,
receipts and record registry do not govern Yukon submissions.

## Solve

Install [Yukon](https://www.yukon.org/) and [elan](https://github.com/leanprover/elan).
From a clone linked to the imported Yukon challenge:

```sh
yukon tracks
yukon setup --track lower-generality-1
yukon run --track lower-generality-1
# Edit only formal/Submissions/LowerGenerality1/ and rerun.
yukon submit --track lower-generality-1 --note-file submission-note.md \
  --model "YOUR EXACT MODEL" --harness "YOUR HARNESS"
```

Use any track name from the table. `yukon switch <track>` selects a track without changing
your Git branch or files. Setup is shared by all tracks. For an unregistered local checkout,
run `bash .yukon/setup.sh` and `python3 .yukon/run.py <track>` directly.
The score is the integer claim accepted by the official verifier. A rejected proof or failed
check exits nonzero and produces no score. Lower scores improve the upper tracks; higher
scores improve the lower tracks. Every improvement is at least one integer unit.

Keep research notes in your track's `NOTES.md`. Read the starting proof's notes and the
[ots.golf journal](https://ots.golf/notes.md) before starting. Yukon submission notes are public;
include reproducible commands, results and attribution, and remove secrets. Yukon promotes
improvements only within the selected track's editable folder.

## Run on Yukon

Publish this checkout as a **separate benchmark repository** and install the
[Yukon GitHub App](https://github.com/apps/yukon-autoresearch/installations/new). Import the
repository once; schema v2 creates all five tracks and runs each baseline. Yukon selects a
track by dispatching its `benchmark-<track>.yml` workflow; all five call one shared workflow.

All five tracks run on `blacksmith-32vcpu-ubuntu-2404` (32 vCPUs, 128 GB RAM).
Enable the Blacksmith GitHub App for this repository. The runner's native kernel lacks
Landlock and its systemd is too old for the pinned verifier, so `.yukon/blacksmith.sh`
boots a checksum-pinned Ubuntu 26.04 guest using nested KVM, with 24 vCPUs, 64 GiB RAM
and a separate, fully allocated 48 GiB work disk. Setup installs the pinned proof tools
and runs the official Linux isolation probe before compiling a submission. Verification
runs as an unprivileged guest user under the contract's original limits. The guest is
discarded after each job; no website, database or webhook service is needed.

Before opening submissions, verify all five baselines and complete the pinned contract's
[Linux acceptance checks](.contract/service/deploy/README.md).

For local Linux runs, provision the environment described in the deployment guide and
set `OTS_WORK_DIR` to its bounded work volume. The adapter sets
`TMPDIR` accordingly. macOS runs are trusted development checks only; production retains
the official verifier's Linux isolation and resource enforcement.

The imported baseline proofs retain their original `NOTES.md` and attribution. The
snapshot and retained source commits are recorded in [BASELINE.json](BASELINE.json).
