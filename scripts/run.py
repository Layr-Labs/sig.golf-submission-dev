"""Adapt the pinned verifier's successful diagnostic result to Yukon's numeric score."""
import json
import os
from pathlib import Path
import subprocess
import sys

score_path = Path("scripts/score.json")
score_path.unlink(missing_ok=True)
env = dict(os.environ)
env.pop("BENCHMARK_INSECURE_LOCAL", None)
command = [sys.executable, ".contract/verifier/verify.py", "full", "--source", ".", "--json"]
if env.get("GITHUB_SHA"):
    command += ["--commit", env["GITHUB_SHA"]]
result = subprocess.run(command, env=env, stdout=subprocess.PIPE, text=True)
print(result.stdout, end="")
if result.returncode:
    raise SystemExit(result.returncode)
report = json.loads(result.stdout)
if report["status"] != "verified":
    raise SystemExit("Verifier did not accept the submission")
sigma, hverify = report["sigma"], report["hverify"]
if type(sigma) is not int or type(hverify) is not int or min(sigma, hverify) <= 0:
    raise SystemExit("Invalid verifier metrics")
score = sigma * hverify
if report["score"] != str(score) or score > 2**53 - 1:
    raise SystemExit("Score is inconsistent or exceeds Yukon's exact integer range")
metrics = {key: report[key] for key in (
    "sigma", "hverify", "contract", "claim_version", "hash_meter", "ranked",
)}
temporary = score_path.with_suffix(".tmp")
temporary.write_text(json.dumps({"score": score, "metrics": metrics}) + "\n")
temporary.replace(score_path)
