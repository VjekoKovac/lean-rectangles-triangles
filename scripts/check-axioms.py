"""Run Lean's reports and compare the complete transitive axiom sets with the allowlist."""
import json
import re
import subprocess
from pathlib import Path

root = Path(__file__).resolve().parent.parent
command = ["lake", "env", "lean", "AxiomReport.lean"]
result = subprocess.run(command, cwd=root, capture_output=True, text=True)
print("$ " + " ".join(command))
print(result.stdout, end="")
print(result.stderr, end="")
result.check_returncode()
config = json.loads((root / "comparator.json").read_text())
allowed = {"propext", "Classical.choice", "Quot.sound"}
if set(config["permitted_axioms"]) != allowed:
    raise SystemExit("Unexpected axiom policy in comparator.json")
targets = re.findall(r"^#print axioms ([\w.]+)$", (root / "AxiomReport.lean").read_text(), re.M)
if targets != config["theorem_names"]:
    raise SystemExit("The axiom report and Comparator must check the same named theorems")
records = re.findall(r"'([\w.]+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", result.stdout)
if [name for name, _ in records] != targets or not targets:
    raise SystemExit("A report is missing or repeated")
for name, contents in records:
    used = set(filter(None, (axiom.strip() for axiom in contents.split(","))))
    if used - allowed:
        raise SystemExit(f"Unexpected axioms for {name}: {sorted(used - allowed)}")
print(f"Accepted {len(records)} axiom reports")
