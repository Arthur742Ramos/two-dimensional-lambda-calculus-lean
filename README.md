# Two-dimensional typed lambda calculus in Lean

This repository formalizes the central non-collapse result from Daniel O.
Martínez-Rivillas, Arthur F. Ramos, and Ruy J. G. B. de Queiroz's manuscript
*A Theory of a Two-Dimensional Typed Lambda Calculus*.

The calculus retains conversion evidence as data. A `Step` is tagged as beta,
eta, congruence, reflexivity, symmetry, or transitivity; a `Path` is a finite
sequence of steps. `Step2` contains the paper's full declared family of
two-dimensional generators: typed beta, eta, and lambda-congruence squares;
structural coherence; cancellation; congruence functoriality; and whiskering.
`Path2` stores finite pastings of these cells.

The principal theorem assigns a Boolean structural parity to every path and
proves that all `Step2` and `Path2` witnesses preserve it. The beta contraction
of `(fun x => f x) a` has parity one, while eta contraction of `f` inside the
application context has parity zero. Therefore no declared two-cell or finite
pasting identifies the two routes, despite their definitionally equal source
and target. Their composite also gives a loop that cannot be connected to the
empty path.

## Scope

The formalized results correspond to Definitions 2.1, 2.2, and 3.1 and
Theorem 7.3 and Corollary 7.5 of the manuscript. The Lean development also
formalizes the nontrivial-loop consequence discussed immediately after
Corollary 7.5.

This first Palomar entry does not claim normalization or completeness for a
standalone lambda syntax, a semantic interpretation in higher lambda models,
an infinity-groupoid, or a computation of the fundamental group of the circle.
It also does not yet port the path-algebra, certified-naturality, and transport
constructions in Sections 4–6, or the Idris refutation of unrestricted
naturality. Those are separate follow-up milestones.

## Build and verify

The project has no external Lean dependencies and is pinned to Lean 4.28.0.

```console
lake build
./scripts/check.sh
```

The Palomar surface is deliberately small:

- `Challenge.lean` states the calculus and the four recorded results.
- `Solution.lean` supplies proofs by structural induction.
- `comparator.json` selects those declarations and permits only `propext`.
- `formalization.yaml` records provenance, scope, fidelity, and automation.

Lean's `#print axioms` reports no axiom dependencies for the four selected
proofs. The Comparator configuration nevertheless allowlists `propext` because
the exported Lean environment declares it and NanoDa requires every exported
axiom declaration to be permitted.

The complete Comparator and NanoDa replay is available through
`./scripts/verify-comparator.sh`; it provisions exact pinned verifier revisions
under `.cache/`, which is ignored by Git.

Palomar submissions go through <https://submit.palomar-registry.org/>.

## Trust boundary

Lean checks the definitions and proofs relative to its kernel. The independent
NanoDa replay checks the exported proof terms. Neither check validates the
paper's broader philosophical discussion, the cited literature, or a semantic
interpretation not represented in the Lean declarations.

## License

The Lean source and repository documentation are licensed under Apache-2.0.
The cited manuscript remains under its authors' own terms and is not included
in this repository.
