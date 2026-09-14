# Recommended Palomar submission

Submit **one entry**, selecting `submission-comparator.json`. The two other
configurations are retained as independently verified regression subsets, not
as additional proposed registrations.

## Exact intake choices

- Repository: `Arthur742Ramos/two-dimensional-lambda-calculus-lean`
- Commit: use the full 40-character SHA of the final green CI commit supplied
  with this handoff; do not enter a branch or tag.
- Comparator configuration: `submission-comparator.json`
- Project directory: leave blank (repository root).
- Formalization metadata: `formalization.yaml` (leaving the default blank has
  the same effect).
- Existing Palomar ID: leave blank for this first registration.
- Relationship: **I am a responsible author or maintainer of it**, if submitting
  as Arthur F. Ramos. This is a personal authorization declaration, not a proof
  inferred by the verifier.

The title and abstract are taken from the committed `formalization.yaml`.
Do not substitute a broader claim of full lambda-calculus formalization.

## Statement of record

The proposed title is **Certified naturality and the obstruction to unrestricted
naturality in a typed two-dimensional calculus**.

The single configuration selects 48 declarations, organized around one question:
which homotopies carry naturality in this evidence calculus?

| Result family | Formal anchors | Role |
|---|---|---|
| Canonical presented evaluation | `evalHomotopyStepI` and its seven equations | Fixes the evaluated evidence and constructs its certificate |
| Finite naturality and transport | `certifiedPathNaturality`, `transportAlongPathI`, `certifiedPathTransport`, `recoverNaturalityFromPathTransport` | Positive result for finite global presentations |
| Unrestricted-naturality obstruction | `Refutation.noBadPath2`, `Refutation.notStepNat`, `Refutation.notNatPath` | Concrete negative result, via a noncommutative invariant |
| Non-collapse | `betaEtaSeparated`, `betaEtaLoopNontrivial` | Distinguishes labelled conversion evidence under the declared cells |
| Standalone syntax bridge | `Syntax.representationAdequacy`, `Syntax.interpret_parity`, `Syntax.Example.interpretedRoutesSeparated` | Establishes a precise syntactic representation and evidence interpretation |

Unlisted rows of the configuration are computation equations and supporting
invariant, preservation, or recovery lemmas. They are not advertised as separate
research discoveries. The full argument and counterexample are in README.md and
PROOF_GUIDE.md; all statement dependencies occur directly in the self-contained
SubmissionChallenge.lean, with no project-specific imports.

## Qualifications that must accompany the entry

1. The refutation is classical and permits `propext`, `Quot.sound`, and
   `Classical.choice`. It does not verify the claimed constructive Idris proof.
2. Standalone syntax adequacy is representation adequacy for well-typed raw
   trees, not full abstraction, denotational completeness, or normalization.
3. The host evidence calculus has definitionally equal beta/eta endpoints.
   The additional syntax has genuinely distinct syntactic endpoints, and the
   interpretation preserves the displayed evidence distinction.
4. Transport comparison uses the constructed step-naturality certificates;
   it is not an independent proof of their naturality.
5. The manuscript's three authors are credited as source authors. The new Lean
   proof is an independent formal reconstruction, not a novelty/priority claim.

## Verification and review boundary

`scripts/check.sh` runs the builds, regression tests, core and extension axiom
audits, dependency checks, declaration preflight, and challenge size checks.
CI independently runs Comparator/NanoDa on the combined package and both
regression subsets. The combined challenge is below the hard 1,000-line/100-KiB
limits, but above the 300-line auditability-warning threshold. The length reflects
an explicit full cell signature and the positive/negative theorem boundaries.

Green CI is evidence for the prepared artifact, not a Palomar verification
report or an editorial acceptance. Palomar runs its own checks. Read its private
review before deciding whether to register; registration publishes the review
and creates persistent source-preservation records. This preparation has not
created an intake or registered anything.
