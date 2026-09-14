#!/usr/bin/env bash
set -euo pipefail
repository_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
cd "$repository_root"

if rg -n '\b(sorry|admit|oops|axiom)\b' Syntax.lean Refutation.lean Extensions.lean; then
  echo "Extension implementation contains a proof hole or custom axiom" >&2
  exit 1
fi

dependencies=$(lake env lean --src-deps ExtensionChallenge.lean)
while IFS= read -r dependency; do
  case "$dependency" in
    */src/lean/*) ;;
    *) echo "Extension challenge has a non-core dependency: $dependency" >&2; exit 1 ;;
  esac
done <<< "$dependencies"

lake env lean --run scripts/CompareDeclarations.lean extensions-comparator.json

report=$(lake env lean scripts/ExtensionAxiomAudit.lean)
printf '%s\n' "$report"
EXTENSION_AXIOM_REPORT="$report" python3 - <<'PY'
import json
import os
import re
from pathlib import Path

allowed = {"propext", "Quot.sound", "Classical.choice"}
lines = os.environ["EXTENSION_AXIOM_REPORT"].splitlines()
assert len(lines) == 17, lines
for line in lines:
    if "does not depend on any axioms" in line:
        continue
    match = re.fullmatch(r"'[^']+' depends on axioms: \[([^]]*)\]", line)
    assert match, line
    assert set(match[1].split(", ")) <= allowed, line
config = json.loads(Path("extensions-comparator.json").read_text())
assert config["challenge_module"] == "ExtensionChallenge"
assert config["solution_module"] == "Extensions"
assert config["enable_nanoda"] is True
assert set(config["permitted_axioms"]) == allowed
assert len(config["theorem_names"]) == 16
assert config["definition_names"] == ["TDLC.Syntax.interpret"]
audited = {re.match(r"'([^']+)'", line)[1] for line in lines}
assert set(config["theorem_names"] + config["definition_names"]) == audited
src = Path("ExtensionChallenge.lean").read_text()
assert len(src.splitlines()) <= 1000
assert len(src.encode()) <= 102400
PY

lake env lean scripts/ExtensionTests.lean
git diff --check
