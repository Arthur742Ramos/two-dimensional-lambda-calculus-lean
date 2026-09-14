/-!
# Certified naturality and the obstruction to unrestricted naturality

This single challenge records the boundary of naturality in the declared typed
two-dimensional conversion calculus. Canonically presented homotopies have
constructed naturality and transport witnesses. In contrast, an explicit family
on Fin 3 has a naturality boundary admitting no Step2 or finite Path2 witness.

The negative proof is classical and uses a noncommutative invariant; this is not
a verification of the manuscript's claimed constructive Idris proof. All
generators of Step2 below are retained, not selected to fit the invariant.

Supporting results preserve beta/eta evidence separation and connect a standalone
typed de Bruijn syntax to the host calculus. Syntax adequacy means exact
representation of extrinsically typed raw terms, not denotational completeness.
See the repository README for provenance, research motivation, and exact scope.
-/

namespace TDLC

universe u

/-- Labelled one-step conversions between terms. -/
inductive Step : {α : Type u} → α → α → Type (u + 1) where
  | beta {A B : Type u} (f : A → B) (a : A) :
      Step ((fun x => f x) a) (f a)
  | eta {A B : Type u} (f : A → B) :
      Step (fun x => f x) f
  | apCong {A B : Type u} (f : A → B) {x y : A} :
      Step x y → Step (f x) (f y)
  | lamCong {A B : Type u} {f g : A → B} :
      ((x : A) → Step (f x) (g x)) → Step f g
  | refl {A : Type u} (x : A) : Step x x
  | sym {A : Type u} {x y : A} : Step x y → Step y x
  | trans {A : Type u} {x y z : A} : Step x y → Step y z → Step x z

/-- Finite sequences of labelled steps. -/
inductive Path : {α : Type u} → α → α → Type (u + 1) where
  | nil {A : Type u} (x : A) : Path x x
  | seq {A : Type u} {x y z : A} : Step x y → Path y z → Path x z

namespace Path

/-- Concatenation, recursively exposing the first path. -/
def concat {A : Type u} {x y z : A} : Path x y → Path y z → Path x z
  | .nil _, q => q
  | .seq s p, q => .seq s (concat p q)

infixr:65 " ++ₚ " => concat

/-- Embed one step as a singleton path. -/
def lEmbed {A : Type u} {x y : A} (s : Step x y) : Path x y :=
  .seq s (.nil y)

/-- Reverse a path and explicitly symmetrise every step. -/
def inv {A : Type u} {x y : A} : Path x y → Path y x
  | .nil _ => .nil _
  | .seq s p => inv p ++ₚ lEmbed (.sym s)

/-- Functorial action of a host-language function on labelled paths. -/
def ap {A B : Type u} (f : A → B) {x y : A} : Path x y → Path (f x) (f y)
  | .nil _ => .nil _
  | .seq s p => .seq (.apCong f s) (ap f p)

/-- Compress a path into one structural step. -/
def toStep {A : Type u} {x y : A} : Path x y → Step x y
  | .nil _ => .refl _
  | .seq s p => .trans s (toStep p)

end Path

/-- Host-language eta expansion, named so its congruence remains visible. -/
def etaExpand {A B : Type u} (f : A → B) : A → B := fun x => f x

/-- Two-cells between parallel paths, with exactly the generators used by the paper. -/
inductive Step2 : {A : Type u} → {x y : A} → Path x y → Path x y → Type (u + 1) where
  | cReflStep {A : Type u} {x y : A} (s : Step x y) :
      Step2 (Path.lEmbed (.refl x) ++ₚ Path.lEmbed s)
        (Path.lEmbed s ++ₚ Path.lEmbed (.refl y))
  | betaStep {A B : Type u} (f : A → B) {a b : A} (s : Step a b) :
      Step2 (Path.ap (fun x => f x) (Path.lEmbed s) ++ₚ Path.lEmbed (.beta f b))
        (Path.lEmbed (.beta f a) ++ₚ Path.ap f (Path.lEmbed s))
  | etaStep {A B : Type u} {f g : A → B} (s : Step f g) :
      Step2 (Path.ap etaExpand (Path.lEmbed s) ++ₚ Path.lEmbed (.eta g))
        (Path.lEmbed (.eta f) ++ₚ Path.lEmbed s)
  | lamCongStep {A B : Type u} {f g : A → B}
      (h : (x : A) → Step (f x) (g x)) {a b : A} (s : Step a b) :
      Step2
        (Path.ap f (Path.lEmbed s) ++ₚ
          Path.lEmbed (.apCong (fun k : A → B => k b) (.lamCong h)))
        (Path.lEmbed (.apCong (fun k : A → B => k a) (.lamCong h)) ++ₚ
          Path.ap g (Path.lEmbed s))
  | refl2 {A : Type u} {x y : A} (p : Path x y) : Step2 p p
  | sym2 {A : Type u} {x y : A} {p q : Path x y} : Step2 p q → Step2 q p
  | trans2 {A : Type u} {x y : A} {p q r : Path x y} :
      Step2 p q → Step2 q r → Step2 p r
  | reflStep2 {A : Type u} (x : A) :
      Step2 (Path.lEmbed (.refl x)) (.nil x)
  | symStep2 {A : Type u} {x y : A} (s : Step x y) :
      Step2 (Path.lEmbed (.sym s)) (Path.inv (Path.lEmbed s))
  | transStep2 {A : Type u} {x y z : A} (s : Step x y) (t : Step y z) :
      Step2 (Path.lEmbed (.trans s t)) (Path.lEmbed s ++ₚ Path.lEmbed t)
  | leftInvStep2 {A : Type u} {x y : A} (s : Step x y) :
      Step2 (Path.inv (Path.lEmbed s) ++ₚ Path.lEmbed s) (.nil y)
  | rightInvStep2 {A : Type u} {x y : A} (s : Step x y) :
      Step2 (Path.lEmbed s ++ₚ Path.inv (Path.lEmbed s)) (.nil x)
  | symSymStep2 {A : Type u} {x y : A} (s : Step x y) :
      Step2 (Path.lEmbed (.sym (.sym s))) (Path.lEmbed s)
  | apCongIdStep2 {A : Type u} {x y : A} (s : Step x y) :
      Step2 (Path.ap (fun t => t) (Path.lEmbed s)) (Path.lEmbed s)
  | apCongStep2 {A B : Type u} (f : A → B) {x y : A} {p q : Path x y} :
      Step2 p q → Step2 (Path.ap f p) (Path.ap f q)
  | apCongComposeStep2 {A B C : Type u} (g : B → C) (f : A → B)
      {x y : A} (s : Step x y) :
      Step2 (Path.ap g (Path.ap f (Path.lEmbed s)))
        (Path.ap (fun z => g (f z)) (Path.lEmbed s))
  | cong2 {A : Type u} {x y z : A} (s : Step x y) {p q : Path y z} :
      Step2 p q → Step2 (.seq s p) (.seq s q)
  | whiskR2 {A : Type u} {w x y : A} {p q : Path w x} :
      Step2 p q → (r : Path x y) → Step2 (p ++ₚ r) (q ++ₚ r)

/-- Sequences of two-cells retain an explicit pasting presentation. -/
inductive Path2 {A : Type u} {x y : A} : (p q : Path x y) → Type (u + 1) where
  | nil2 (p : Path x y) : Path2 p p
  | seq2 {p q r : Path x y} : Step2 p q → Path2 q r → Path2 p r

/-- An inductive language of globally presented pointwise step homotopies. -/
inductive HomotopyStepI : {A B : Type u} → (A → B) → (A → B) → Type (u + 1) where
  | refl {A B : Type u} (f : A → B) : HomotopyStepI f f
  | beta {A B : Type u} (f : A → B) : HomotopyStepI (fun x => f x) f
  | eta {A B : Type u} :
      HomotopyStepI (@etaExpand A B) (fun f => f)
  | apCong {A B C : Type u} (v : B → C) {f g : A → B} :
      HomotopyStepI f g →
      HomotopyStepI (fun x => v (f x)) (fun x => v (g x))
  | sym {A B : Type u} {f g : A → B} :
      HomotopyStepI f g → HomotopyStepI g f
  | trans {A B : Type u} {f g k : A → B} :
      HomotopyStepI f g → HomotopyStepI g k → HomotopyStepI f k
  | lamCong {A B : Type u} {f g : A → B} :
      HomotopyStepI f g → HomotopyStepI f g

/-- A computed pointwise family paired with its naturality square for every path. -/
structure CertifiedStepEvaluation {A B : Type u} {f g : A → B}
    (e : HomotopyStepI f g) : Type (u + 1) where
  family : (x : A) → Step (f x) (g x)
  naturality : {x y : A} → (p : Path x y) →
    Step2
      (Path.ap f p ++ₚ Path.lEmbed (family y))
      (Path.lEmbed (family x) ++ₚ Path.ap g p)

/-- Canonical structural-recursive evaluation of the presented language. -/
def evalHomotopyStepI {A B : Type u} {f g : A → B}
    (e : HomotopyStepI f g) : CertifiedStepEvaluation e := by
  sorry

/-- The evaluator's reflexivity equation. -/
theorem evalHomotopyStepI_refl {A B : Type u} (f : A → B) (x : A) :
    (evalHomotopyStepI (.refl f)).family x = Step.refl (f x) := by
  sorry

/-- The evaluator's beta equation. -/
theorem evalHomotopyStepI_beta {A B : Type u} (f : A → B) (x : A) :
    (evalHomotopyStepI (.beta f)).family x = Step.beta f x := by
  sorry

/-- The evaluator's eta equation. -/
theorem evalHomotopyStepI_eta {A B : Type u} (f : A → B) :
    (evalHomotopyStepI (@HomotopyStepI.eta A B)).family f = Step.eta f := by
  sorry

/-- The evaluator's postcomposition equation. -/
theorem evalHomotopyStepI_apCong {A B C : Type u} (v : B → C)
    {f g : A → B} (e : HomotopyStepI f g) (x : A) :
    (evalHomotopyStepI (.apCong v e)).family x =
      Step.apCong v ((evalHomotopyStepI e).family x) := by
  sorry

/-- The evaluator's symmetry equation. -/
theorem evalHomotopyStepI_sym {A B : Type u} {f g : A → B}
    (e : HomotopyStepI f g) (x : A) :
    (evalHomotopyStepI (.sym e)).family x =
      Step.sym ((evalHomotopyStepI e).family x) := by
  sorry

/-- The evaluator's transitivity equation. -/
theorem evalHomotopyStepI_trans {A B : Type u} {f g k : A → B}
    (e : HomotopyStepI f g) (d : HomotopyStepI g k) (x : A) :
    (evalHomotopyStepI (.trans e d)).family x =
      Step.trans ((evalHomotopyStepI e).family x)
        ((evalHomotopyStepI d).family x) := by
  sorry

/-- The evaluator's lambda-congruence equation. -/
theorem evalHomotopyStepI_lamCong {A B : Type u} {f g : A → B}
    (e : HomotopyStepI f g) (x : A) :
    (evalHomotopyStepI (.lamCong e)).family x =
      Step.apCong (fun k : A → B => k x)
        (Step.lamCong (evalHomotopyStepI e).family) := by
  sorry

/-- Every presented step homotopy receives a constructed naturality square. -/
def certifiedStepNaturality {A B : Type u} {f g : A → B}
    (e : HomotopyStepI f g) {x y : A} (p : Path x y) :
    Step2
      (Path.ap f p ++ₚ Path.lEmbed ((evalHomotopyStepI e).family y))
      (Path.lEmbed ((evalHomotopyStepI e).family x) ++ₚ Path.ap g p) := by
  sorry

/-- A global finite presentation made from certified step presentations. -/
inductive HomotopyPathI : {A B : Type u} → (A → B) → (A → B) → Type (u + 1) where
  | nil {A B : Type u} (f : A → B) : HomotopyPathI f f
  | seq {A B : Type u} {f g k : A → B} :
      HomotopyStepI f g → HomotopyPathI g k → HomotopyPathI f k

/-- Pointwise evaluation of a global presented homotopy path. -/
def evalHomotopyPathI {A B : Type u} {f g : A → B}
    (hp : HomotopyPathI f g) (x : A) : Path (f x) (g x) := by
  sorry

theorem evalHomotopyPathI_nil {A B : Type u} (f : A → B) (x : A) :
    evalHomotopyPathI (.nil f) x = Path.nil (f x) := by
  sorry

theorem evalHomotopyPathI_seq {A B : Type u} {f g k : A → B}
    (e : HomotopyStepI f g) (hp : HomotopyPathI g k) (x : A) :
    evalHomotopyPathI (.seq e hp) x =
      Path.seq ((evalHomotopyStepI e).family x) (evalHomotopyPathI hp x) := by
  sorry

/-- Direct naturality retained as an explicit finite two-path. -/
def certifiedPathNaturality {A B : Type u} {f g : A → B}
    (hp : HomotopyPathI f g) {x y : A} (p : Path x y) :
    Path2
      (Path.ap f p ++ₚ evalHomotopyPathI hp y)
      (evalHomotopyPathI hp x ++ₚ Path.ap g p) := by
  sorry

/-- Conjugation transport along one canonically evaluated step presentation. -/
def transportAlongPresented {A B : Type u} {f g : A → B}
    (e : HomotopyStepI f g) (x y : A) (q : Path (f x) (f y)) :
    Path (g x) (g y) := by
  sorry

/-- Conjugation transport respects every finite two-path. -/
def transportAlongPresentedRespects {A B : Type u} {f g : A → B}
    (e : HomotopyStepI f g) {x y : A} {q r : Path (f x) (f y)}
    (cells : Path2 q r) :
    Path2 (transportAlongPresented e x y q) (transportAlongPresented e x y r) := by
  sorry

/-- Transport compares source and target congruence as an explicit two-path. -/
def certifiedTransport {A B : Type u} {f g : A → B}
    (e : HomotopyStepI f g) {x y : A} (p : Path x y) :
    Path2 (transportAlongPresented e x y (Path.ap f p)) (Path.ap g p) := by
  sorry

/-- A comparison out of transport recovers the corresponding naturality square. -/
def recoverNaturalityFromTransport {A B : Type u} {f g : A → B}
    (e : HomotopyStepI f g) {x y : A} {q : Path (f x) (f y)}
    {r : Path (g x) (g y)}
    (cells : Path2 (transportAlongPresented e x y q) r) :
    Path2
      (q ++ₚ Path.lEmbed ((evalHomotopyStepI e).family y))
      (Path.lEmbed ((evalHomotopyStepI e).family x) ++ₚ r) := by
  sorry

/-- Naturality reconstructed through transport, whose comparison uses step naturality. -/
def certifiedNaturalityViaTransport {A B : Type u} {f g : A → B}
    (e : HomotopyStepI f g) {x y : A} (p : Path x y) :
    Path2
      (Path.ap f p ++ₚ Path.lEmbed ((evalHomotopyStepI e).family y))
      (Path.lEmbed ((evalHomotopyStepI e).family x) ++ₚ Path.ap g p) := by
  sorry

/-- Recursive transport along an arbitrary finite global presentation. -/
def transportAlongPathI {A B : Type u} {f g : A → B} :
    (hp : HomotopyPathI f g) → (x y : A) →
    Path (f x) (f y) → Path (g x) (g y) := by
  sorry

theorem transportAlongPathI_nil {A B : Type u} (f : A → B)
    (x y : A) (q : Path (f x) (f y)) :
    transportAlongPathI (.nil f) x y q = q := by
  sorry

theorem transportAlongPathI_seq {A B : Type u} {f g k : A → B}
    (e : HomotopyStepI f g) (hp : HomotopyPathI g k)
    (x y : A) (q : Path (f x) (f y)) :
    transportAlongPathI (.seq e hp) x y q =
      transportAlongPathI hp x y (transportAlongPresented e x y q) := by
  sorry

/-- Recursive transport preserves finite two-path witnesses. -/
def transportAlongPathIRespects {A B : Type u} {f g : A → B} :
    (hp : HomotopyPathI f g) → {x y : A} → {q r : Path (f x) (f y)} →
    Path2 q r →
    Path2 (transportAlongPathI hp x y q) (transportAlongPathI hp x y r) := by
  sorry

/-- The comparison is derived from step naturality, recursively over the presentation. -/
def certifiedPathTransport {A B : Type u} {f g : A → B} :
    (hp : HomotopyPathI f g) → {x y : A} → (p : Path x y) →
    Path2 (transportAlongPathI hp x y (Path.ap f p)) (Path.ap g p) := by
  sorry

/-- Recover a square from any comparison out of recursive transport. -/
def recoverNaturalityFromPathTransport {A B : Type u} {f g : A → B} :
    (hp : HomotopyPathI f g) → {x y : A} →
    {q : Path (f x) (f y)} → {r : Path (g x) (g y)} →
    Path2 (transportAlongPathI hp x y q) r →
    Path2 (q ++ₚ evalHomotopyPathI hp y) (evalHomotopyPathI hp x ++ₚ r) := by
  sorry

/-- A transport-based reconstruction, not an independent proof of naturality. -/
def certifiedPathNaturalityViaTransport {A B : Type u} {f g : A → B}
    (hp : HomotopyPathI f g) {x y : A} (p : Path x y) :
    Path2 (Path.ap f p ++ₚ evalHomotopyPathI hp y)
      (evalHomotopyPathI hp x ++ₚ Path.ap g p) := by
  sorry

namespace Step

/-- The outer constructor of a step. -/
def headTag {A : Type u} {x y : A} : Step x y → Nat
  | @TDLC.Step.beta _ _ f a => 0
  | @TDLC.Step.eta _ _ f => 1
  | @TDLC.Step.apCong _ _ f _ _ s => 2
  | @TDLC.Step.lamCong _ _ f g h => 3
  | @TDLC.Step.refl _ x => 4
  | @TDLC.Step.sym _ _ _ s => 5
  | @TDLC.Step.trans _ _ _ _ s t => 6

end Step

/-- A global presentation evaluates to the same outer step form at every point. -/
theorem evaluatedHeadTagConstant {A B : Type u} {f g : A → B}
    (e : HomotopyStepI f g) (x y : A) :
    Step.headTag ((evalHomotopyStepI e).family x) =
      Step.headTag ((evalHomotopyStepI e).family y) := by
  sorry

/-- A semantic family whose evidence form genuinely varies by point. -/
def mixedUnitFamily : (b : Bool) → Step Unit.unit Unit.unit
  | false => .beta (fun x : Unit => x) Unit.unit
  | true => .refl Unit.unit

/-- Presented homotopies form a proper subclass of semantic pointwise families. -/
theorem semanticFamilyNotPresented :
    ¬ ∃ e : HomotopyStepI (fun _ : Bool => Unit.unit) (fun _ : Bool => Unit.unit),
      ∀ b, (evalHomotopyStepI e).family b = mixedUnitFamily b := by
  sorry

/-- Boolean exclusive-or, used as addition in the two-element grading. -/
def bxor : Bool → Bool → Bool
  | false, b => b
  | true, false => true
  | true, true => false

namespace Step

/-- Structural parity: beta contributes one; eta and lambda congruence contribute zero. -/
def parity {A : Type u} {x y : A} : Step x y → Bool
  | @TDLC.Step.beta _ _ f a => true
  | @TDLC.Step.eta _ _ f => false
  | @TDLC.Step.apCong _ _ f _ _ s => parity s
  | @TDLC.Step.lamCong _ _ f g h => false
  | @TDLC.Step.refl _ x => false
  | @TDLC.Step.sym _ _ _ s => parity s
  | @TDLC.Step.trans _ _ _ _ s t => bxor (parity s) (parity t)

end Step

namespace Path

/-- XOR-sum of structural parities along a path. -/
def parity {A : Type u} {x y : A} : Path x y → Bool
  | .nil _ => false
  | .seq s p => bxor (Step.parity s) (parity p)

end Path

/-- Every declared generating or composite two-cell preserves structural parity. -/
theorem step2PreservesParity {A : Type u} {x y : A} {p q : Path x y}
    (cell : Step2 p q) : Path.parity p = Path.parity q := by
  sorry

/-- Every finite sequence of two-cells preserves structural parity. -/
theorem path2PreservesParity {A : Type u} {x y : A} {p q : Path x y}
    (cells : Path2 p q) : Path.parity p = Path.parity q := by
  sorry

/-- The beta-labelled and eta-labelled routes with the same endpoints cannot be joined. -/
theorem betaEtaSeparated {A B : Type u} (f : A → B) (a : A) :
    Step2
      (Path.lEmbed (Step.beta f a))
      (Path.lEmbed (Step.apCong (fun k : A → B => k a) (Step.eta f))) → False := by
  sorry

/-- The beta/eta loop is not connected by any two-path to the empty path. -/
theorem betaEtaLoopNontrivial {A B : Type u} (f : A → B) (a : A) :
    Path2
      (Path.lEmbed (Step.beta f a) ++ₚ
        Path.inv (Path.lEmbed (Step.apCong (fun k : A → B => k a) (Step.eta f))))
      (.nil (f a)) → False := by
  sorry

end TDLC

namespace TDLC.Syntax

/-- Simple object types generated by one base type and function types. -/
inductive Ty where
  | base
  | arr : Ty → Ty → Ty
  deriving DecidableEq, Repr

/-- Typed de Bruijn variables: zero selects the newest binder and succ skips one. -/
inductive Var : List Ty → Ty → Type where
  | zero : Var (a :: Γ) a
  | succ : Var Γ a → Var (b :: Γ) a

/-- Intrinsic simply typed lambda terms; indices enforce scope and typing. -/
inductive Tm : List Ty → Ty → Type where
  | var : Var Γ a → Tm Γ a
  | app : Tm Γ (.arr a b) → Tm Γ a → Tm Γ b
  | lam : Tm (a :: Γ) b → Tm Γ (.arr a b)

/-- An independent, untyped tree grammar with annotated lambda binders. -/
inductive Raw where
  | var : Nat → Raw
  | app : Raw → Raw → Raw
  | lam : Ty → Raw → Raw
  deriving DecidableEq, Repr

/-- Erase a typed variable to its de Bruijn position. -/
def Var.index : Var Γ a → Nat
  | .zero => 0
  | .succ v => v.index + 1

/-- Erase intrinsic typing to the annotated raw term tree. -/
def erase : Tm Γ a → Raw
  | .var v => .var v.index
  | .app f x => .app (erase f) (erase x)
  | @Tm.lam a _ _ t => .lam a (erase t)

/-- Extrinsic context lookup at a natural-number de Bruijn position. -/
inductive Lookup : List Ty → Nat → Ty → Type where
  | zero : Lookup (a :: Γ) 0 a
  | succ : Lookup Γ n a → Lookup (b :: Γ) (n + 1) a

/-- The ordinary extrinsic typing rules for annotated raw lambda terms. -/
inductive HasType : List Ty → Raw → Ty → Type where
  | var : Lookup Γ n a → HasType Γ (.var n) a
  | app : HasType Γ f (.arr a b) → HasType Γ x a → HasType Γ (.app f x) b
  | lam : HasType (a :: Γ) t b → HasType Γ (.lam a t) (.arr a b)

/-- Construct the context-lookup derivation for a typed variable. -/
def Var.lookup : (v : Var Γ a) → Lookup Γ v.index a
  | .zero => .zero
  | .succ v => .succ v.lookup

/-- Reconstruct a typed variable from an extrinsic lookup derivation. -/
def Lookup.variable : Lookup Γ n a → Var Γ a
  | .zero => .zero
  | .succ h => .succ h.variable

theorem Lookup.index_variable (h : Lookup Γ n a) : h.variable.index = n := by
  sorry

/-- Every intrinsic term yields an extrinsic typing derivation for its erasure. -/
def eraseTyped : (t : Tm Γ a) → HasType Γ (erase t) a
  | .var v => .var v.lookup
  | .app f x => .app (eraseTyped f) (eraseTyped x)
  | .lam t => .lam (eraseTyped t)

/-- Reconstruct an intrinsic term from an extrinsic typing derivation. -/
def elaborate : HasType Γ r a → Tm Γ a
  | .var h => .var h.variable
  | .app f x => .app (elaborate f) (elaborate x)
  | .lam t => .lam (elaborate t)

theorem erase_elaborate (h : HasType Γ r a) : erase (elaborate h) = r := by
  sorry

/-- Representation adequacy: exactly the extrinsically well-typed trees are represented. -/
theorem representationAdequacy (Γ : List Ty) (r : Raw) (a : Ty) :
    Nonempty (HasType Γ r a) ↔ ∃ t : Tm Γ a, erase t = r := by
  sorry

/-- Type-preserving maps of variables between contexts. -/
abbrev Ren (Γ Δ : List Ty) := ∀ {a}, Var Γ a → Var Δ a

/-- Extend a renaming under a binder, fixing its newly bound variable. -/
def Ren.lift (r : Ren Γ Δ) : Ren (a :: Γ) (a :: Δ)
  | _, .zero => .zero
  | _, .succ v => .succ (r v)

/-- Capture-avoiding action of a variable renaming on terms. -/
def rename (r : Ren Γ Δ) : Tm Γ a → Tm Δ a
  | .var v => .var (r v)
  | .app f x => .app (rename r f) (rename r x)
  | .lam t => .lam (rename r.lift t)

/-- Simultaneous, type-preserving substitutions of terms for variables. -/
abbrev Sub (Γ Δ : List Ty) := ∀ {a}, Var Γ a → Tm Δ a

/-- Lift substitution under a binder by weakening substituted free terms. -/
def Sub.lift (s : Sub Γ Δ) : Sub (a :: Γ) (a :: Δ)
  | _, .zero => .var .zero
  | _, .succ v => rename (fun v => .succ v) (s v)

/-- Capture-avoiding simultaneous substitution by structural recursion. -/
def subst (s : Sub Γ Δ) : Tm Γ a → Tm Δ a
  | .var v => s v
  | .app f x => .app (subst s f) (subst s x)
  | .lam t => .lam (subst s.lift t)

/-- Substitute one argument for the newest variable and preserve older variables. -/
def single (x : Tm Γ a) : Sub (a :: Γ) Γ
  | _, .zero => x
  | _, .succ v => .var v

/-- Syntactic eta expansion using weakening and a fresh de Bruijn variable. -/
def etaExpand (f : Tm Γ (.arr a b)) : Tm Γ (.arr a b) :=
  .lam (.app (rename (fun v => .succ v) f) (.var .zero))

/-- Interpret simple types using an arbitrary set for the base type. -/
def Denote (U : Type) : Ty → Type
  | .base => U
  | .arr a b => Denote U a → Denote U b

/-- A valuation assigning appropriately typed values to the context variables. -/
abbrev Env (U : Type) (Γ : List Ty) := ∀ {a}, Var Γ a → Denote U a

/-- Extend a valuation with the value of a newly bound variable. -/
def Env.extend (ρ : Env U Γ) (x : Denote U a) : Env U (a :: Γ)
  | _, .zero => x
  | _, .succ v => ρ v

/-- Set-valued interpretation of intrinsic terms in a variable environment. -/
def eval (t : Tm Γ a) (ρ : Env U Γ) : Denote U a :=
  match t with
  | .var v => ρ v
  | .app f x => eval f ρ (eval x ρ)
  | .lam t => fun x => eval t (ρ.extend x)

theorem eval_congr (t : Tm Γ a) {ρ σ : Env U Γ}
    (h : ∀ {a} (v : Var Γ a), ρ v = σ v) : eval t ρ = eval t σ := by
  sorry

theorem eval_rename (t : Tm Γ a) (r : Ren Γ Δ) (ρ : Env U Δ) :
    eval (rename r t) ρ = eval t (fun v => ρ (r v)) := by
  sorry

theorem eval_subst (t : Tm Γ a) (s : Sub Γ Δ) (ρ : Env U Δ) :
    eval (subst s t) ρ = eval t (fun v => eval (s v) ρ) := by
  sorry

theorem eval_beta (t : Tm (a :: Γ) b) (x : Tm Γ a) (ρ : Env U Γ) :
    eval (subst (single x) t) ρ = eval t (ρ.extend (eval x ρ)) := by
  sorry

theorem eval_eta (f : Tm Γ (.arr a b)) (ρ : Env U Γ) :
    eval (etaExpand f) ρ = eval f ρ := by
  sorry

/-- Object-language conversion evidence, with genuinely syntactic endpoints. -/
inductive Conv : Tm Γ a → Tm Γ a → Type where
  | beta (t : Tm (a :: Γ) b) (x : Tm Γ a) :
      Conv (.app (.lam t) x) (subst (single x) t)
  | eta (f : Tm Γ (.arr a b)) : Conv (etaExpand f) f
  | appLeft {f g : Tm Γ (.arr a b)} : Conv f g → (x : Tm Γ a) →
      Conv (.app f x) (.app g x)
  | appRight (f : Tm Γ (.arr a b)) {x y : Tm Γ a} : Conv x y →
      Conv (.app f x) (.app f y)
  | lam {t s : Tm (a :: Γ) b} : Conv t s → Conv (.lam t) (.lam s)
  | refl (t : Tm Γ a) : Conv t t
  | sym {t s : Tm Γ a} : Conv t s → Conv s t
  | trans {t s r : Tm Γ a} : Conv t s → Conv s r → Conv t r

/-- Transport labelled evidence along equalities of its host endpoints. -/
def castStep {A : Type} {x y x' y' : A}
    (hx : x = x') (hy : y = y') (s : TDLC.Step x y) : TDLC.Step x' y' :=
  hx ▸ hy ▸ s

/-- Interpretation transports endpoints by substitution/eta correctness;
it retains beta, eta and congruence labels rather than replacing them by equality. -/
def interpret {t s : Tm Γ a} : (c : Conv t s) → (ρ : Env U Γ) →
    TDLC.Step (eval t ρ) (eval s ρ)
  | .beta t x, ρ =>
      castStep rfl (eval_beta t x ρ).symm
        (.beta (fun v => eval t (ρ.extend v)) (eval x ρ))
  | .eta f, ρ =>
      castStep (eval_eta f ρ).symm rfl (.eta (eval f ρ))
  | .appLeft c x, ρ => .apCong (fun f => f (eval x ρ)) (interpret c ρ)
  | .appRight f c, ρ => .apCong (eval f ρ) (interpret c ρ)
  | .lam c, ρ => .lamCong (fun x => interpret c (ρ.extend x))
  | .refl t, ρ => .refl (eval t ρ)
  | .sym c, ρ => .sym (interpret c ρ)
  | .trans c d, ρ => .trans (interpret c ρ) (interpret d ρ)

/-- The grading records conversion evidence, not reduction length. -/
def Conv.parity {t s : Tm Γ a} : Conv t s → Bool
  | .beta _ _ => true
  | .eta _ => false
  | .appLeft c _ => c.parity
  | .appRight _ c => c.parity
  | .lam _ => false
  | .refl _ => false
  | .sym c => c.parity
  | .trans c d => bxor c.parity d.parity

theorem parity_cast {A : Type} {x y x' y' : A}
    (hx : x = x') (hy : y = y') (s : TDLC.Step x y) :
    TDLC.Step.parity (castStep hx hy s) = TDLC.Step.parity s := by
  sorry

theorem interpret_parity {t s : Tm Γ a} (c : Conv t s) (ρ : Env U Γ) :
    TDLC.Step.parity (interpret c ρ) = c.parity := by
  sorry

/-- Different grades reflect non-identification by the full host two-cell theory. -/
theorem noCell_of_parity_ne {t s : Tm Γ a} (c d : Conv t s)
    (hne : c.parity ≠ d.parity) (ρ : Env U Γ) :
    ¬ Nonempty (TDLC.Path2 (TDLC.Path.lEmbed (interpret c ρ))
      (TDLC.Path.lEmbed (interpret d ρ))) := by
  sorry

namespace Example

/-- Example context containing a unary function and its argument. -/
abbrev Γ := [Ty.arr .base .base, Ty.base]
/-- The function variable in the example context. -/
def fn : Tm Γ (.arr .base .base) := .var .zero
/-- The argument variable in the example context. -/
def arg : Tm Γ .base := .var (.succ .zero)
/-- Application of the eta-expanded function, the shared syntactic source. -/
def source : Tm Γ .base := .app (etaExpand fn) arg
/-- Direct function application, the shared syntactic target. -/
def target : Tm Γ .base := .app fn arg

/-- The beta contraction from the shared source to the target. -/
def betaRoute : Conv source target :=
  .beta (.app (.var (.succ .zero)) (.var .zero)) arg

/-- The eta contraction under application from the same source to the target. -/
def etaRoute : Conv source target := .appLeft (.eta fn) arg

theorem endpointsDistinct : source ≠ target := by
  sorry

theorem routesDistinct : betaRoute ≠ etaRoute := by
  sorry

theorem interpretedRoutesSeparated (ρ : Env U Γ) :
    ¬ Nonempty (TDLC.Path2 (TDLC.Path.lEmbed (interpret betaRoute ρ))
      (TDLC.Path.lEmbed (interpret etaRoute ρ))) := by
  sorry

end Example

end TDLC.Syntax


/-! A noncommutative invariant for all declared two-cells. Unlike Boolean parity,
this invariant can detect failure of an unrestricted naturality square. -/

namespace TDLC.Refutation

universe u v

/-- Group operations and explicit laws used by the noncommutative invariant. -/
structure GroupData (G : Type v) where
  one : G
  mul : G → G → G
  inv : G → G
  one_mul : ∀ x, mul one x = x
  mul_one : ∀ x, mul x one = x
  assoc : ∀ x y z, mul (mul x y) z = mul x (mul y z)
  inv_mul : ∀ x, mul (inv x) x = one
  mul_inv : ∀ x, mul x (inv x) = one
  inv_one : inv one = one
  inv_inv : ∀ x, inv (inv x) = x

/-- A function is constant when all of its values agree. -/
def Constant {A B : Type u} (f : A → B) : Prop := ∀ x y, f x = f y

/-- All host endpoints are propositionally equal; their evidence need not be. -/
theorem endpoints {A : Type u} {x y : A} (s : Step x y) : x = y := by
  sorry

/-- A marker need not be natural in its type arguments. -/
abbrev Marker := (A B : Type u) → A → B → B

variable {G : Type v} (g : GroupData G) (mark : Marker.{u})

/-- Interpret steps in a group: application changes valuation, and constant beta steps carry marker differences. -/
noncomputable def grade (g : GroupData G) (mark : Marker.{u})
    {A : Type u} {x y : A} : Step x y → (A → G) → G
  | @Step.beta A B f a, val =>
      if Classical.propDecidable (Constant f) |>.decide then
        g.mul (g.inv (val (f a))) (val (mark A B a (f a)))
      else g.one
  | .eta _, _ => g.one
  | .apCong f s, val => grade g mark s (fun x => val (f x))
  | .lamCong _, _ => g.one
  | .refl _, _ => g.one
  | .sym s, val => g.inv (grade g mark s val)
  | .trans s t, val => g.mul (grade g mark s val) (grade g mark t val)

/-- Multiply the group values of a finite sequence of labelled steps. -/
noncomputable def pathGrade (g : GroupData G) (mark : Marker.{u})
    {A : Type u} {x y : A} : Path x y → (A → G) → G
  | .nil _, _ => g.one
  | .seq s p, val => g.mul (grade g mark s val) (pathGrade g mark p val)

theorem grade_constant {A : Type u} {x y : A} (s : Step x y)
    (val : A → G) (c : G) (hc : ∀ x, val x = c) : grade g mark s val = g.one := by
  sorry

theorem pathGrade_embed {A : Type u} {x y : A} (s : Step x y) (val : A → G) :
    pathGrade g mark (Path.lEmbed s) val = grade g mark s val := by
  sorry

theorem pathGrade_concat {A : Type u} {x y z : A} (p : Path x y) (q : Path y z)
    (val : A → G) : pathGrade g mark (p ++ₚ q) val =
      g.mul (pathGrade g mark p val) (pathGrade g mark q val) := by
  sorry

theorem pathGrade_ap {A B : Type u} (f : A → B) {x y : A}
    (p : Path x y) (val : B → G) :
    pathGrade g mark (Path.ap f p) val = pathGrade g mark p (fun x => val (f x)) := by
  sorry

theorem cell_preserves {A : Type u} {x y : A} {p q : Path x y}
    (cell : Step2 p q) (val : A → G) : pathGrade g mark p val = pathGrade g mark q val := by
  sorry

theorem path2_preserves {A : Type u} {x y : A} {p q : Path x y}
    (cells : Path2 p q) (val : A → G) : pathGrade g mark p val = pathGrade g mark q val := by
  sorry

/-- The six-element dihedral group; all laws are checked by finite reduction. -/
def dMul (x y : Fin 6) : Fin 6 :=
  Fin.ofNat 6 (((x.val % 3 + (if x.val < 3 then y.val % 3 else 3 - y.val % 3)) % 3) +
    (if (x.val < 3) = (y.val < 3) then 0 else 3))

/-- Inversion in the six-element dihedral group encoding. -/
def dInv (x : Fin 6) : Fin 6 :=
  if x.val < 3 then Fin.ofNat 6 ((3 - x.val) % 3) else x

/-- The concrete group structure on Fin 6, with every law proved by finite reduction. -/
def dihedral : GroupData (Fin 6) where
  one := 0
  mul := dMul
  inv := dInv
  one_mul := by decide
  mul_one := by decide
  assoc := by decide
  inv_mul := by decide
  mul_inv := by decide
  inv_one := by decide
  inv_inv := by decide

/-- The marker uses its argument when source and target types coincide. -/
noncomputable def diagonalMarker : Marker.{0} := by
  classical
  exact fun A B a b => if h : A = B then cast h a else b

theorem diagonalMarker_self (A : Type) (a b : A) : diagonalMarker A A a b = a := by
  sorry

/-- Assign identity and two distinct reflections to the three object values. -/
def valuation (x : Fin 3) : Fin 6 := if x = 0 then 0 else if x = 1 then 3 else 4

/-- An arbitrary pointwise family, deliberately not a presented evaluator. -/
def badFamily (x : Fin 3) : Step x x :=
  .beta (fun _ : Fin 3 => x) 1

/-- The beta loop at zero used to test the pointwise family's naturality. -/
def testStep : Step (0 : Fin 3) 0 := .beta (fun _ : Fin 3 => 0) 2
/-- The singleton path of the chosen beta loop. -/
def testPath : Path (0 : Fin 3) 0 := Path.lEmbed testStep

/-- The mapped loop followed by the endpoint component of the pointwise family. -/
def badLeft : Path (0 : Fin 3) 0 :=
  Path.ap (fun x : Fin 3 => x) testPath ++ₚ Path.lEmbed (badFamily 0)

/-- The endpoint component followed by the mapped loop, in the opposite order. -/
def badRight : Path (0 : Fin 3) 0 :=
  Path.lEmbed (badFamily 0) ++ₚ Path.ap (fun x : Fin 3 => x) testPath

theorem grade_constantBeta (x a : Fin 3) :
    grade dihedral diagonalMarker (Step.beta (fun _ : Fin 3 => x) a) valuation =
      dMul (dInv (valuation x)) (valuation a) := by
  sorry

theorem badLeft_grade : pathGrade dihedral diagonalMarker badLeft valuation = 1 := by
  sorry

theorem badRight_grade : pathGrade dihedral diagonalMarker badRight valuation = 2 := by
  sorry

theorem noBadPath2 : ¬ Nonempty (Path2 badLeft badRight) := by
  sorry

theorem noBadStep2 : ¬ Nonempty (Step2 badLeft badRight) := by
  sorry

/-- Unrestricted step naturality, at universe zero. -/
def StepNat : Type 1 :=
  {A B : Type} → {f g : A → B} →
    (h : (x : A) → Step (f x) (g x)) → {x y : A} → (s : Step x y) →
    Step2 (Path.ap f (Path.lEmbed s) ++ₚ Path.lEmbed (h y))
      (Path.lEmbed (h x) ++ₚ Path.ap g (Path.lEmbed s))

theorem notStepNat : ¬ Nonempty StepNat := by
  sorry

/-- Even allowing arbitrary finite pastings does not rescue unrestricted naturality. -/
def NatPath : Type 1 :=
  {A B : Type} → {f g : A → B} →
    (h : (x : A) → Path (f x) (g x)) → {x y : A} → (p : Path x y) →
    Path2 (Path.ap f p ++ₚ h y) (h x ++ₚ Path.ap g p)

theorem notNatPath : ¬ Nonempty NatPath := by
  sorry

end TDLC.Refutation
