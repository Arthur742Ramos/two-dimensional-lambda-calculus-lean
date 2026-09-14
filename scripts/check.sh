#!/usr/bin/env bash
set -euo pipefail

repository_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
cd "$repository_root"

lake build
lake env lean scripts/TransportTests.lean
bash scripts/check-extensions.sh

challenge_dependencies=$(lake env lean --src-deps Challenge.lean)
while IFS= read -r dependency; do
  case "$dependency" in
    */src/lean/*) ;;
    *)
      echo "Challenge import closure contains a non-core source: $dependency" >&2
      exit 1
      ;;
  esac
done <<< "$challenge_dependencies"

solution_dependencies=$(lake env lean --src-deps Solution.lean)
while IFS= read -r dependency; do
  case "$dependency" in
    */src/lean/*) ;;
    *)
      echo "Solution import closure contains an unexpected source: $dependency" >&2
      exit 1
      ;;
  esac
done <<< "$solution_dependencies"

axiom_report=$(lake env lean scripts/AxiomAudit.lean 2>&1)
printf '%s\n' "$axiom_report"
if printf '%s\n' "$axiom_report" | rg -n '\b(sorryAx|Lean\.ofReduceBool|axioms: \[[^]]+\])'; then
  echo "Solution depends on a forbidden proof mechanism or an axiom" >&2
  exit 1
fi

challenge_lines=$(wc -l < Challenge.lean | tr -d ' ')
challenge_bytes=$(wc -c < Challenge.lean | tr -d ' ')
if [ "$challenge_lines" -gt 1000 ] || [ "$challenge_bytes" -gt 102400 ]; then
  echo "Challenge.lean exceeds Palomar's 1000-line/100-KiB limits" >&2
  exit 1
fi

challenge_holes=$(rg -c '^[[:space:]]*sorry[[:space:]]*$' Challenge.lean || true)
if [ "$challenge_holes" -ne 31 ]; then
  echo "Challenge.lean must contain exactly 31 deliberate declaration holes" >&2
  exit 1
fi

if rg -n '\b(sorry|admit|oops)\b' Solution.lean TwoDimensionalLambdaCalculus.lean; then
  echo "The proved implementation contains a proof hole" >&2
  exit 1
fi

python3 - <<'PY'
import json
from pathlib import Path

config = json.loads(Path("comparator.json").read_text(encoding="utf-8"))
assert config == {
    "challenge_module": "Challenge",
    "solution_module": "Solution",
    "theorem_names": [
        "TDLC.evalHomotopyStepI_refl",
        "TDLC.evalHomotopyStepI_beta",
        "TDLC.evalHomotopyStepI_eta",
        "TDLC.evalHomotopyStepI_apCong",
        "TDLC.evalHomotopyStepI_sym",
        "TDLC.evalHomotopyStepI_trans",
        "TDLC.evalHomotopyStepI_lamCong",
        "TDLC.evalHomotopyPathI_nil",
        "TDLC.evalHomotopyPathI_seq",
        "TDLC.evaluatedHeadTagConstant",
        "TDLC.semanticFamilyNotPresented",
        "TDLC.transportAlongPathI_nil",
        "TDLC.transportAlongPathI_seq",
        "TDLC.step2PreservesParity",
        "TDLC.path2PreservesParity",
        "TDLC.betaEtaSeparated",
        "TDLC.betaEtaLoopNontrivial",
    ],
    "definition_names": [
        "TDLC.evalHomotopyStepI",
        "TDLC.certifiedStepNaturality",
        "TDLC.evalHomotopyPathI",
        "TDLC.certifiedPathNaturality",
        "TDLC.transportAlongPresented",
        "TDLC.transportAlongPresentedRespects",
        "TDLC.certifiedTransport",
        "TDLC.recoverNaturalityFromTransport",
        "TDLC.certifiedNaturalityViaTransport",
        "TDLC.transportAlongPathI",
        "TDLC.transportAlongPathIRespects",
        "TDLC.certifiedPathTransport",
        "TDLC.recoverNaturalityFromPathTransport",
        "TDLC.certifiedPathNaturalityViaTransport",
    ],
    "permitted_axioms": ["propext"],
    "enable_nanoda": True,
}
assert Path("formalization.yaml").is_file()
assert Path("lake-manifest.json").is_file()
assert Path("LICENSE").is_file()
PY

git diff --check
echo "Checks passed: Challenge.lean is ${challenge_lines} lines/${challenge_bytes} bytes"
