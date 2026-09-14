/-! Independent challenge for standalone syntax and unrestricted naturality.
All foundational generators below are the same as the core challenge. -/
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


end TDLC

namespace TDLC.Syntax

inductive Ty where
  | base
  | arr : Ty → Ty → Ty
  deriving DecidableEq, Repr

inductive Var : List Ty → Ty → Type where
  | zero : Var (a :: Γ) a
  | succ : Var Γ a → Var (b :: Γ) a

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

def Var.index : Var Γ a → Nat
  | .zero => 0
  | .succ v => v.index + 1

def erase : Tm Γ a → Raw
  | .var v => .var v.index
  | .app f x => .app (erase f) (erase x)
  | @Tm.lam a _ _ t => .lam a (erase t)

inductive Lookup : List Ty → Nat → Ty → Type where
  | zero : Lookup (a :: Γ) 0 a
  | succ : Lookup Γ n a → Lookup (b :: Γ) (n + 1) a

inductive HasType : List Ty → Raw → Ty → Type where
  | var : Lookup Γ n a → HasType Γ (.var n) a
  | app : HasType Γ f (.arr a b) → HasType Γ x a → HasType Γ (.app f x) b
  | lam : HasType (a :: Γ) t b → HasType Γ (.lam a t) (.arr a b)

def Var.lookup : (v : Var Γ a) → Lookup Γ v.index a
  | .zero => .zero
  | .succ v => .succ v.lookup

def Lookup.variable : Lookup Γ n a → Var Γ a
  | .zero => .zero
  | .succ h => .succ h.variable

theorem Lookup.index_variable (h : Lookup Γ n a) : h.variable.index = n := by
  sorry

def eraseTyped : (t : Tm Γ a) → HasType Γ (erase t) a
  | .var v => .var v.lookup
  | .app f x => .app (eraseTyped f) (eraseTyped x)
  | .lam t => .lam (eraseTyped t)

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

abbrev Ren (Γ Δ : List Ty) := ∀ {a}, Var Γ a → Var Δ a

def Ren.lift (r : Ren Γ Δ) : Ren (a :: Γ) (a :: Δ)
  | _, .zero => .zero
  | _, .succ v => .succ (r v)

def rename (r : Ren Γ Δ) : Tm Γ a → Tm Δ a
  | .var v => .var (r v)
  | .app f x => .app (rename r f) (rename r x)
  | .lam t => .lam (rename r.lift t)

abbrev Sub (Γ Δ : List Ty) := ∀ {a}, Var Γ a → Tm Δ a

def Sub.lift (s : Sub Γ Δ) : Sub (a :: Γ) (a :: Δ)
  | _, .zero => .var .zero
  | _, .succ v => rename (fun v => .succ v) (s v)

def subst (s : Sub Γ Δ) : Tm Γ a → Tm Δ a
  | .var v => s v
  | .app f x => .app (subst s f) (subst s x)
  | .lam t => .lam (subst s.lift t)

def single (x : Tm Γ a) : Sub (a :: Γ) Γ
  | _, .zero => x
  | _, .succ v => .var v

def etaExpand (f : Tm Γ (.arr a b)) : Tm Γ (.arr a b) :=
  .lam (.app (rename (fun v => .succ v) f) (.var .zero))

def Denote (U : Type) : Ty → Type
  | .base => U
  | .arr a b => Denote U a → Denote U b

abbrev Env (U : Type) (Γ : List Ty) := ∀ {a}, Var Γ a → Denote U a

def Env.extend (ρ : Env U Γ) (x : Denote U a) : Env U (a :: Γ)
  | _, .zero => x
  | _, .succ v => ρ v

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

abbrev Γ := [Ty.arr .base .base, Ty.base]
def fn : Tm Γ (.arr .base .base) := .var .zero
def arg : Tm Γ .base := .var (.succ .zero)
def source : Tm Γ .base := .app (etaExpand fn) arg
def target : Tm Γ .base := .app fn arg

def betaRoute : Conv source target :=
  .beta (.app (.var (.succ .zero)) (.var .zero)) arg

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

def Constant {A B : Type u} (f : A → B) : Prop := ∀ x y, f x = f y

/-- All host endpoints are propositionally equal; their evidence need not be. -/
theorem endpoints {A : Type u} {x y : A} (s : Step x y) : x = y := by
  sorry

/-- A marker need not be natural in its type arguments. -/
abbrev Marker := (A B : Type u) → A → B → B

variable {G : Type v} (g : GroupData G) (mark : Marker.{u})

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

def dInv (x : Fin 6) : Fin 6 :=
  if x.val < 3 then Fin.ofNat 6 ((3 - x.val) % 3) else x

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

def valuation (x : Fin 3) : Fin 6 := if x = 0 then 0 else if x = 1 then 3 else 4

/-- An arbitrary pointwise family, deliberately not a presented evaluator. -/
def badFamily (x : Fin 3) : Step x x :=
  .beta (fun _ : Fin 3 => x) 1

def testStep : Step (0 : Fin 3) 0 := .beta (fun _ : Fin 3 => 0) 2
def testPath : Path (0 : Fin 3) 0 := Path.lEmbed testStep

def badLeft : Path (0 : Fin 3) 0 :=
  Path.ap (fun x : Fin 3 => x) testPath ++ₚ Path.lEmbed (badFamily 0)

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
