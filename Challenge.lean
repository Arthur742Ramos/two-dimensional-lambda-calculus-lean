/-!
# Typed two-dimensional conversion evidence

This file states the Palomar challenge extracted from Sections 2 through 7 of
"A Theory of a Two-Dimensional Typed Lambda Calculus".  `Step` records labelled
one-step conversions, `Path` records finite sequences of steps, and `Step2` and
`Path2` record the declared two-dimensional identifications.  The principal
claims are a canonical evaluator with constructed naturality certificates,
direct and transport-based naturality for finite presentations, and a structural
parity preserved by every cell.  The evaluator is deliberately not identified
with all semantic pointwise families: an explicit family is proved to lie
outside its image.  Finally, beta and eta evidence with common endpoints are
separated, and their composite loop is not connected to the empty path.

The object types are universe-polymorphic but are kept in one universe at a
time.  The evidence families live one universe higher so that function-valued
premises remain inspectable data.
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

/-- Naturality reconstructed independently through conjugation transport. -/
def certifiedNaturalityViaTransport {A B : Type u} {f g : A → B}
    (e : HomotopyStepI f g) {x y : A} (p : Path x y) :
    Path2
      (Path.ap f p ++ₚ Path.lEmbed ((evalHomotopyStepI e).family y))
      (Path.lEmbed ((evalHomotopyStepI e).family x) ++ₚ Path.ap g p) := by
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
