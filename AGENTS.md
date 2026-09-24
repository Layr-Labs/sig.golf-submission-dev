# sig.golf beta benchmark

- Read `README.md` and `.contract/README.md` for the pinned beta rules.
- Solvers edit only `submission/`: `claim.json`, `Solution.lean` and `SigGolfCandidate/`.
- Preserve the protected contract, manifest, setup scripts and workflow in submissions.
- Check with `bash scripts/setup.sh` and `python3 scripts/run.py` on a supported Linux host.
- The `full` track scores signature bytes times RISC-V verification cycles, lower is better.
- `BASELINE.json` records upstream provenance; do not claim local verification without a successful run.
- Yukon handles submission PRs and manual promotions; the upstream bot workflow is not used here.
