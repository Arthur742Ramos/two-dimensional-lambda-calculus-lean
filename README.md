# Two-dimensional typed lambda calculus in Lean

This repository formalizes the constructive core and non-collapse result from Daniel O.
Martínez-Rivillas, Arthur F. Ramos, and Ruy J. G. B. de Queiroz's manuscript
*A Theory of a Two-Dimensional Typed Lambda Calculus*.

The calculus retains conversion evidence as data. A `Step` is tagged as beta,
eta, congruence, reflexivity, symmetry, or transitivity; a `Path` is a finite
sequence of steps. `Step2` contains the paper's full declared family of
two-dimensional generators: typed beta, eta, and lambda-congruence squares;
structural coherence; cancellation; congruence functoriality; and whiskering.
`Path2` stores finite pastings of these cells.

The main positive result is a canonical structural-recursive evaluator for a
seven-constructor language of presented homotopies. Each evaluation produces
both a pointwise step family and naturality squares for every path. The
construction is exposed by equations for reflexivity, beta, eta,
postcomposition, symmetry, transitivity, and lambda congruence; it is not an
unconstrained certificate field. Finite sequences of presentations have direct
`Path2` naturality witnesses. Independently, conjugation transport respects
two-paths, maps source congruence to target congruence, and reconstructs the
same naturality boundary.

The presentation restriction is mathematically visible. Every canonically
evaluated step family has one uniform outer evidence constructor, while the
explicit `mixedUnitFamily` uses beta evidence at `false` and reflexivity at
`true`. Lean proves that no presented homotopy evaluates to this family. This
is a proper-subclass theorem, not a claim that the mixed family admits no
possible naturality square.

The main negative result assigns a Boolean structural parity to every path and
proves that all `Step2` and `Path2` witnesses preserve it. The beta contraction
of `(fun x => f x) a` has parity one, while eta contraction of `f` inside the
application context has parity zero. Therefore no declared two-cell or finite
pasting identifies the two routes, despite their definitionally equal source
and target. Their composite also gives a loop that cannot be connected to the
empty path.

## Scope

The formalized results correspond to Definitions 2.1, 2.2, 3.1, 5.1, 5.2,
5.5, and 6.3; Theorems 5.3 and 6.2; the one-presentation instances of
Proposition 6.4 and Theorems 6.6–6.8; Theorem 7.3; and Corollary 7.5. The Lean
development also formalizes the nontrivial-loop consequence discussed after
Corollary 7.5 and a precise proper-subclass result separating presented from
arbitrary semantic step families.

This first Palomar entry does not claim normalization or completeness for a
standalone lambda syntax, a semantic interpretation in higher lambda models,
an infinity-groupoid, or a computation of the fundamental group of the circle.
It does not yet port transport recursively along an arbitrary function-space
presentation, the claimed Idris refutation of unrestricted naturality, a full
equality theory of `Path2`, or every named path-algebra lemma from Section 4.
The PDF states the unrestricted-naturality refutation but does not include its
proof or source; this repository therefore records only the narrower statement
that has been independently reconstructed and checked in Lean: presented
homotopies are a proper subclass of semantic pointwise families.

## Build and verify

The project has no external Lean dependencies and is pinned to Lean 4.28.0.

```console
lake build
./scripts/check.sh
```

The Palomar surface is deliberately small:

- `Challenge.lean` states the calculus, evaluator equations, naturality and
  transport constructions, the presentation obstruction, and non-collapse.
- `Solution.lean` supplies explicit constructions and proofs by structural
  recursion.
- `comparator.json` selects those declarations and permits only `propext`.
- `formalization.yaml` records provenance, scope, fidelity, and automation.

Lean's `#print axioms` reports no axiom dependencies for every selected
construction and proof. The Comparator configuration nevertheless allowlists
`propext` because the exported Lean environment declares it and NanoDa requires
every exported axiom declaration to be permitted.

The complete Comparator and NanoDa replay is available through
`./scripts/verify-comparator.sh`; it provisions exact pinned verifier revisions
under `.cache/`, which is ignored by Git.

Palomar submissions go through <https://submit.palomar-registry.org/>.

## Trust boundary

All recorded evaluator, naturality, and transport values are ordinary
computable Lean definitions; none is marked `noncomputable`. Lean checks the
definitions and proofs relative to its kernel. The independent
NanoDa replay checks the exported proof terms. Neither check validates the
paper's broader philosophical discussion, the cited literature, or a semantic
interpretation not represented in the Lean declarations.

## License

The Lean source and repository documentation are licensed under Apache-2.0.
The cited manuscript remains under its authors' own terms and is not included
in this repository.
