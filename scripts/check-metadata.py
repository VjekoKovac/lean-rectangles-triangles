"""Check the submission inputs with the upstream schema and Palomar's validator.

Pass the path of the pinned PalomarSubmission source tree and the v0.4 schema
JSON. See evidence/metadata-check.txt for versions, retrieval commands and output.
"""

import hashlib
import json
import sys
from importlib.metadata import version
from pathlib import Path

import jsonschema
import yaml

if len(sys.argv) != 3:
    sys.exit("Usage: python3 scripts/check-metadata.py PALOMAR_SOURCE SCHEMA_JSON")

project = Path(__file__).resolve().parents[1]
palomar = Path(sys.argv[1]).resolve()
schema_bytes = Path(sys.argv[2]).read_bytes()
if hashlib.sha256(schema_bytes).hexdigest() != "25ff6b25ca4511635aff4443cf20480c15e59dddf19591c730950b442ea54fce":
    sys.exit("The schema differs from upstream formalization.yaml v0.4 at the recorded revision.")

sys.path.insert(0, str(palomar))
from scripts import source_requirements, submission_contract, verify_submission

schema = json.loads(schema_bytes)
jsonschema.Draft7Validator.check_schema(schema)
yaml_path = project / "formalization.yaml"
jsonschema.Draft7Validator(schema).validate(yaml.safe_load(yaml_path.read_bytes()))
print("Python", sys.version.split()[0], "| jsonschema", version("jsonschema"), "| PyYAML", version("PyYAML"))
print("formalization.yaml SHA-256:", hashlib.sha256(yaml_path.read_bytes()).hexdigest())
print("Upstream JSON Schema v0.4: PASS")
metadata = submission_contract.load_formalization_metadata(yaml_path)
provenance = submission_contract.normalized_provenance(metadata)
print("Palomar metadata and provenance: PASS")
print("Result origin:", provenance["result_origin"])
print("Repository role:", provenance["repository_role"])
config = verify_submission.load_comparator_config(project / "comparator.json")
alignment = metadata["alignment"]["statements"]
names = [statement["lean"] for statement in alignment]
if names != config["theorem_names"] or len(set(names)) != 4:
    sys.exit("The alignment must enumerate exactly the four Comparator targets in order.")
if any(statement["module"] != config["solution_module"] for statement in alignment):
    sys.exit("The solution module must agree across the alignment and Comparator.")
expected_axioms = {"propext", "Classical.choice", "Quot.sound"}
if set(config["permitted_axioms"]) != expected_axioms or set(metadata["status"]["axioms"]) != expected_axioms:
    sys.exit("Axiom declarations differ from the three specified by the authorship request.")
if metadata["project"]["authors"] != metadata["sources"][0]["authors"]:
    sys.exit("The project and paper author lists differ.")
print("Comparator configuration, four alignment entries, axiom names and author lists: PASS")
toolchain = (project / "lean-toolchain").read_text().strip()
verify_submission.supported_toolchain(toolchain)
print("Supported Lean toolchain:", toolchain)
license_file = verify_submission.repository_license_file(project)
print("Palomar root license file:", license_file.name)
summary, issues = source_requirements.inspect_lean_sources(project)
if issues:
    sys.exit("\n".join(str(issue) for issue in issues))
print("Palomar Lean source-format checks: PASS for", summary["files_checked"], "files")
