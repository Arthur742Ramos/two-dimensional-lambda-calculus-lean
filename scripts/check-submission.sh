#!/usr/bin/env bash
set -euo pipefail
repository_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
cd "$repository_root"
lake env lean --run scripts/CompareDeclarations.lean submission-comparator.json
dependencies=$(lake env lean --src-deps SubmissionChallenge.lean)
while IFS= read -r dependency; do
  case "$dependency" in
    */src/lean/*) ;;
    *) echo "Submission challenge has a non-core dependency: $dependency" >&2; exit 1 ;;
  esac
done <<< "$dependencies"
python3 - <<'PY'
import json
from pathlib import Path

core = json.loads(Path("comparator.json").read_text())
ext = json.loads(Path("extensions-comparator.json").read_text())
combined = json.loads(Path("submission-comparator.json").read_text())
assert combined == {
    "challenge_module": "SubmissionChallenge",
    "solution_module": "Extensions",
    "theorem_names": core["theorem_names"] + ext["theorem_names"],
    "definition_names": core["definition_names"] + ext["definition_names"],
    "permitted_axioms": ext["permitted_axioms"],
    "enable_nanoda": True,
}
names = combined["theorem_names"] + combined["definition_names"]
assert len(names) == len(set(names)) == 48
src = Path("SubmissionChallenge.lean").read_text()
assert len(src.splitlines()) <= 1000
assert len(src.encode()) <= 102400
print(f"Submission boundary: {len(names)} declarations, {len(src.splitlines())} lines, {len(src.encode())} bytes")
PY
