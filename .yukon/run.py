#!/usr/bin/env python3
"""Publish a Yukon score only after the pinned ots.golf verifier accepts it."""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]


def run(root: Path, track: str) -> int:
    manifest = json.loads((root / "benchmark.json").read_text())
    selected = next((t for t in manifest["tracks"] if t["name"] == track), None)
    if selected is None:
        raise ValueError(f"unknown track: {track}")
    score_path = root / selected["scorePath"]
    score_path.parent.mkdir(parents=True, exist_ok=True)
    # A failed rerun must never leave yesterday's accepted score behind.
    score_path.unlink(missing_ok=True)
    command = [sys.executable, str(root / ".contract/verifier/verify.py"),
               track, "--source", str(root), "--json"]
    env = os.environ.copy()
    if sys.platform.startswith("linux") and env.get("OTS_WORK_DIR"):
        env["TMPDIR"] = env["OTS_WORK_DIR"]
    completed = subprocess.run(command, cwd=root, env=env, text=True, capture_output=True)
    (score_path.parent / "verdict.json").write_text(completed.stdout)
    if completed.stderr:
        print(completed.stderr, file=sys.stderr, end="")
    print(completed.stdout, end="")
    verdict = json.loads(completed.stdout)
    claim = verdict.get("claim")
    if (completed.returncode != 0 or verdict.get("status") != "verified"
            or verdict.get("track") != track):
        return 1
    limits = json.loads((root / ".contract/challenges.json").read_text())["limits"]
    if type(claim) is not int or not 0 <= claim <= limits["max_claim"]:
        raise ValueError("verified result has an invalid claim")
    # Use the claim in the trusted verdict, never reread the editable claim file.
    score_path.write_text(json.dumps({"score": claim, "metrics": {
        "verified": True, "track": track,
        "verificationSeconds": verdict.get("duration_s"),
    }}, indent=2) + "\n")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("track")
    args = parser.parse_args()
    try:
        return run(ROOT, args.track)
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(f"Benchmark failed: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
