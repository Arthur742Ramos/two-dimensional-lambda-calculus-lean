# What the extensions prove

## A genuine counterexample to unrestricted naturality

Take the identity functions on `Fin 3`. Define the pointwise family
`h(x) = beta (constant x) 1`, and take the loop
`p = [beta (constant 0) 2]` at zero. The naturality square would identify
`ap id p · [h(0)]` with `[h(0)] · ap id p`.

To separate them, interpret labelled paths in a group. For a valuation `v`
of object values in that group:

- Application congruence precomposes the valuation with the function.
- Reflexivity, eta, and lambda congruence have the identity value.
- Symmetry uses inversion; transitivity and path concatenation use multiplication.
- A beta step for a constant function has value `v(f(a))⁻¹ v(marker(A,B,a,f(a)))`.
  Beta steps for nonconstant functions have the identity value.

The key lemma is that a constant valuation gives every step the identity value.
Consequently the beta naturality generator is sound: if its function is constant,
the mapped step is trivial; otherwise its beta factors are trivial. The two beta
factors agree because the source step's host endpoints are equal. Lambda
congruence also has equal endpoint functions, by function extensionality.
The remaining generators follow from the group laws and valuation composition.
`cell_preserves` checks **every** constructor; `path2_preserves` checks all finite
pastings. There is no restriction to a hand-picked subset of two-cells.

The marker returns its input argument when its domain and codomain types agree,
and its fallback value otherwise. The proof chooses the six-element dihedral
group, encoded by `Fin 6`, with identity 0. All group laws are proved by kernel
reduction using `decide`, not an unchecked external computation. Set
`v(0)=0`, `v(1)=3`, and `v(2)=4`. The boundaries then have grades
`4*3=1` and `3*4=2`, which are distinct. This proves both `noBadStep2` and
`noBadPath2`, and hence the universal operations `StepNat` and `NatPath` cannot
have inhabitants. The latter formulation even permits a finite `Path2` result,
so it also rules out the paper's stronger single-`Step2` version.

**Trust qualification:** deciding constancy of arbitrary functions and equality
of arbitrary types is classical. This reconstructed proof uses exactly the
standard Lean axioms `propext`, `Quot.sound`, and `Classical.choice`. It does not
establish that the original Idris proof is constructive or correct. It also does
not contradict certified naturality: this particular family is not supplied by
the certified presentation language.

## Standalone syntax and precise adequacy

`Tm Γ a` is an inductive de Bruijn syntax, not a Lean function disguised as a term.
`Raw` is a separate annotated tree grammar, and `HasType Γ raw a` is its extrinsic
typing judgment. The representation theorem states:

> A raw tree has a typing derivation exactly when it is the erasure of a typed term.

The forward direction computes a typed term from the derivation and proves its
erasure is the original tree. The reverse direction builds a typing derivation
from each typed term. Thus this is **representation adequacy**, not a claim of
full abstraction or completeness of a set-valued denotational model.

Renaming and lifted simultaneous substitution implement capture avoidance.
Their interpretation lemmas prove the beta and eta equations. The conversion
interpretation retains evidence constructors and preserves the original parity
grading; it does not replace all conversions with reflexivity. In particular,
the displayed beta and eta routes have syntactically distinct endpoints and
their interpreted evidence is separated by every host two-path.

Still outside scope: normalization, denotational completeness, and a full
standalone two-dimensional syntactic presentation with a two-way adequacy theorem.
These are not prerequisites for the precise representation and evidence results
proved here, and are not silently included in the word “adequacy.”
