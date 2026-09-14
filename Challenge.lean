/-!
# Typed two-dimensional conversion evidence

This file states the Palomar challenge extracted from Sections 2, 3, and 7 of
"A Theory of a Two-Dimensional Typed Lambda Calculus".  `Step` records labelled
one-step conversions, `Path` records finite sequences of steps, and `Step2` and
`Path2` record the declared two-dimensional identifications.  The principal
claim is that a structural parity is preserved by every cell.  Consequently,
the beta contraction of `(fun x => u x) a` and the eta contraction inside the
application context are distinct evidence with the same endpoints, and their
composite gives a loop that is not connected to the empty path.

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
