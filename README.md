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
`Path2` naturality witnesses. Recursive transport along arbitrary finite
presentations respects two-paths, maps source congruence to target congruence,
and reconstructs the same naturality boundary. Its comparison proof uses the
step evaluator's naturality certificates: this is a derived transport theorem,
not an independent proof of naturality. The nil and sequence equations fix the
transport operation explicitly.

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

## Standalone syntax and unrestricted naturality

`Syntax.lean` adds a standalone simply typed de Bruijn calculus: object types,
variables, application, abstraction, renaming, and capture-avoiding substitution.
`representationAdequacy` proves that its terms represent exactly the annotated
raw trees accepted by an independent extrinsic typing judgment. Substitution,
beta, and eta are sound under interpretation. `interpret` maps labelled
syntactic conversions to host `Step` evidence and preserves parity. A concrete
beta/eta pair has provably distinct syntactic source and target, and its two
interpreted routes remain unconnected by any host `Path2`.

`Refutation.lean` proves the stronger negative result: `notStepNat` and
`notNatPath` refute unrestricted naturality, even when arbitrary finite
two-paths are allowed. The counterexample uses an identity function on `Fin 3`,
a pointwise beta family, and a beta loop. A noncommutative dihedral-group
invariant gives the two square boundaries different values while preserving
every declared `Step2` constructor. This is an independent **classical** Lean
proof, not a port or verification of the manuscript's claimed constructive
Idris proof. See [PROOF_GUIDE.md](PROOF_GUIDE.md) for the construction and trust boundary.

## Scope

The formalized results correspond to Definitions 2.1, 2.2, 3.1, 5.1, 5.2,
5.5, and 6.3; Theorems 5.3 and 6.2; transport preservation, comparison, and
recovery for finite presentations corresponding to Proposition 6.4 and
Theorems 6.6–6.8; Theorem 7.3; and Corollary 7.5. The Lean
development also formalizes the nontrivial-loop consequence discussed after
Corollary 7.5 and a precise proper-subclass result separating presented from
arbitrary semantic step families.

This first Palomar entry does not claim normalization or completeness for a
standalone lambda syntax, a semantic interpretation in higher lambda models,
an infinity-groupoid, or a computation of the fundamental group of the circle.
It does not port the original Idris refutation proof, a full equality theory of
`Path2`, or every named path-algebra lemma from Section 4. The standalone syntax
and representation theorem are additional Lean results, not purported source
theorems from the manuscript.

In particular, `mixedUnitFamily` is not established as a counterexample to naturality: its
failure to have a global presentation does not establish the absence of a
two-cell. The actual refutation uses `Refutation.badFamily`, a different family.
The core encoding still uses Lean values and functions. The standalone syntax
does not: its representation adequacy and evidence interpretation are explicit.
These results do not assert completeness of denotational equality for syntactic
conversion, full abstraction, or a separate syntactic two-cell presentation.

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
- `ExtensionChallenge.lean` is a second self-contained challenge for the new
  syntax and refutation; `Extensions.lean` imports their proved modules.
- `extensions-comparator.json` selects 17 extension declarations and explicitly
  allows the standard axioms `propext`, `Quot.sound`, and `Classical.choice`.

Lean's `#print axioms` reports no axiom dependencies for the 35 audited core
constructions and proofs. The core Comparator configuration nevertheless allowlists
`propext` because the exported Lean environment declares it and NanoDa requires
every exported axiom declaration to be permitted.

The complete Comparator and NanoDa replay is available through
`./scripts/verify-comparator.sh`; it provisions exact pinned verifier revisions
under `.cache/`, which is ignored by Git.
Run `./scripts/verify-comparator.sh extensions-comparator.json` for the extension
replay. CI runs both configurations. The extension audit separately checks the
17 new selected declarations against the three named standard axioms; it does
not describe them as axiom-free.

Palomar submissions go through <https://submit.palomar-registry.org/>.

## Trust boundary

All recorded evaluator, naturality, and transport values are ordinary
computable Lean definitions; none is marked `noncomputable`. The refutation's
invariant and type-dependent marker are explicitly `noncomputable`, and its
proof depends on classical choice. The syntax interpretation uses extensionality.
No custom axioms or proof holes occur in the implementation. Lean checks the
definitions and proofs relative to its kernel. The independent
NanoDa replay checks the exported proof terms. Neither check validates the
paper's broader philosophical discussion, the cited literature, or a semantic
interpretation not represented in the Lean declarations.

## License

The Lean source and repository documentation are licensed under Apache-2.0.
The cited manuscript remains under its authors' own terms and is not included
in this repository.
