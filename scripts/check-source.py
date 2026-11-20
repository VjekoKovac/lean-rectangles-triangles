"""Check the intended statement/proof split and compare the explicit theorem target lists."""
import json
import re
from pathlib import Path

root = Path(__file__).resolve().parent.parent
config = json.loads((root / "comparator.json").read_text())
required = ["RTS.combinatorial_growth", "RTS.quantitative_transference",
            "RTS.configuration_lower_bounds", "RTS.trigonometric_growth"]
if config["theorem_names"] != required or config["definition_names"]:
    raise SystemExit("Unexpected Comparator targets")
files = [p for p in root.rglob("*.lean") if ".lake" not in p.parts]
for file in files:
    source = file.read_text()
    if not source.startswith("module\n") or len(source.splitlines()) > 10000:
        raise SystemExit(f"Module header or length issue in {file.relative_to(root)}")
    if file.name != "Challenge.lean":
        if re.search(r"^\s*(?:(?:public|private|meta)\s+)*import\s+Challenge\b", source, re.M):
            raise SystemExit(f"Challenge imported by {file.relative_to(root)}")
        if re.search(r"\b(?:sorry|sorryAx|admit|native_decide|ofReduceBool)\b|^\s*axiom\s", source, re.M):
            raise SystemExit(f"Unexpected proof placeholder or trust primitive in {file.relative_to(root)}")
challenge = (root / "Challenge.lean").read_text()
assert len(challenge.splitlines()) <= 1000 and len(challenge.encode()) <= 102400
imports = re.findall(r"^(?:public )?import\s+([^\s]+)", challenge, re.M)
assert imports and all(module.startswith("Mathlib.") for module in imports)
assert re.findall(r"^theorem\s+(\w+)\s*:", challenge, re.M) == [s.split(".")[1] for s in required]
assert len(re.findall(r":= by sorry\b", challenge)) == 4
print(f"Checked {len(files)} module headers, the Challenge imports and its four target declarations")
