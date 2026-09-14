import Solution

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
  induction s with
  | beta => rfl
  | eta => rfl
  | apCong f s ih => exact congrArg f ih
  | lamCong h ih => exact funext ih
  | refl => rfl
  | sym s ih => exact ih.symm
  | trans s t ihs iht => exact ihs.trans iht

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
  induction s with
  | beta f a =>
      simp only [grade]
      split <;> simp only [hc, g.inv_mul]
  | eta => rfl
  | apCong f s ih => exact ih (fun x => val (f x)) (fun x => hc (f x))
  | lamCong => rfl
  | refl => rfl
  | sym s ih => simp only [grade, ih val hc, g.inv_one]
  | trans s t ihs iht => simp only [grade, ihs val hc, iht val hc, g.one_mul]

theorem pathGrade_embed {A : Type u} {x y : A} (s : Step x y) (val : A → G) :
    pathGrade g mark (Path.lEmbed s) val = grade g mark s val := g.mul_one _

theorem pathGrade_concat {A : Type u} {x y z : A} (p : Path x y) (q : Path y z)
    (val : A → G) : pathGrade g mark (p ++ₚ q) val =
      g.mul (pathGrade g mark p val) (pathGrade g mark q val) := by
  induction p with
  | nil => exact (g.one_mul _).symm
  | seq s p ih => simp only [Path.concat, pathGrade, ih, g.assoc]

theorem pathGrade_ap {A B : Type u} (f : A → B) {x y : A}
    (p : Path x y) (val : B → G) :
    pathGrade g mark (Path.ap f p) val = pathGrade g mark p (fun x => val (f x)) := by
  induction p with
  | nil => rfl
  | seq s p ih => simp only [Path.ap, pathGrade, grade, ih]

theorem cell_preserves {A : Type u} {x y : A} {p q : Path x y}
    (cell : Step2 p q) (val : A → G) : pathGrade g mark p val = pathGrade g mark q val := by
  classical
  induction cell with
  | cReflStep s =>
      simp only [pathGrade_concat, pathGrade_embed, grade, g.one_mul, g.mul_one]
  | betaStep f s =>
      have he := endpoints s
      cases he
      simp only [pathGrade_concat, pathGrade_ap, pathGrade_embed, grade]
      split
      next hc =>
        rename_i a
        have constant : Constant f := of_decide_eq_true hc
        have hg := grade_constant g mark s (fun x => val (f x)) (val (f a))
          (fun x => congrArg val (constant x a))
        rw [hg, g.one_mul, g.mul_one]
      next => simp only [g.one_mul, g.mul_one]
  | etaStep s =>
      simp only [pathGrade_concat, pathGrade_ap, pathGrade_embed, grade,
        g.one_mul, g.mul_one]
      rfl
  | lamCongStep h s =>
      have he := endpoints (Step.lamCong h)
      cases he
      simp only [pathGrade_concat, pathGrade_ap, pathGrade_embed, grade,
        g.one_mul, g.mul_one]
  | refl2 => rfl
  | sym2 c ih => exact (ih val).symm
  | trans2 c d ihc ihd => exact (ihc val).trans (ihd val)
  | reflStep2 => exact g.mul_one _
  | symStep2 s => simp only [Path.inv, Path.lEmbed, Path.concat, pathGrade, grade]
  | transStep2 s t =>
      simp only [pathGrade_embed, pathGrade_concat, grade]
  | leftInvStep2 s =>
      simp only [Path.inv, Path.lEmbed, Path.concat, pathGrade, grade,
        g.mul_one, g.inv_mul]
  | rightInvStep2 s =>
      simp only [Path.inv, Path.lEmbed, Path.concat, pathGrade, grade,
        g.mul_one, g.mul_inv]
  | symSymStep2 s => simp only [pathGrade_embed, grade, g.inv_inv]
  | apCongIdStep2 s => simp only [pathGrade_ap]
  | apCongStep2 f c ih => simpa only [pathGrade_ap] using ih (fun x => val (f x))
  | apCongComposeStep2 f h s => simp only [pathGrade_ap]
  | cong2 s c ih => simp only [pathGrade, ih]
  | whiskR2 c r ih => simp only [pathGrade_concat, ih]

theorem path2_preserves {A : Type u} {x y : A} {p q : Path x y}
    (cells : Path2 p q) (val : A → G) : pathGrade g mark p val = pathGrade g mark q val := by
  induction cells with
  | nil2 => rfl
  | seq2 c cs ih => exact (cell_preserves g mark c val).trans ih

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
  simp [diagonalMarker]

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
  classical
  have hc : Constant (fun _ : Fin 3 => x) := fun _ _ => rfl
  simp only [grade, decide_eq_true hc, if_true, diagonalMarker_self]
  rfl

theorem badLeft_grade : pathGrade dihedral diagonalMarker badLeft valuation = 1 := by
  simp only [badLeft, testPath, testStep, badFamily, pathGrade_concat,
    pathGrade_ap, pathGrade_embed]
  change dMul (grade dihedral diagonalMarker (Step.beta (fun _ : Fin 3 => 0) 2) valuation)
    (grade dihedral diagonalMarker (Step.beta (fun _ : Fin 3 => 0) 1) valuation) = 1
  rw [grade_constantBeta, grade_constantBeta]
  decide

theorem badRight_grade : pathGrade dihedral diagonalMarker badRight valuation = 2 := by
  simp only [badRight, testPath, testStep, badFamily, pathGrade_concat,
    pathGrade_ap, pathGrade_embed]
  change dMul (grade dihedral diagonalMarker (Step.beta (fun _ : Fin 3 => 0) 1) valuation)
    (grade dihedral diagonalMarker (Step.beta (fun _ : Fin 3 => 0) 2) valuation) = 2
  rw [grade_constantBeta, grade_constantBeta]
  decide

theorem noBadPath2 : ¬ Nonempty (Path2 badLeft badRight) := by
  intro ⟨cells⟩
  have h := path2_preserves dihedral diagonalMarker cells valuation
  rw [badLeft_grade, badRight_grade] at h
  exact (by decide : (1 : Fin 6) ≠ 2) h

theorem noBadStep2 : ¬ Nonempty (Step2 badLeft badRight) := by
  intro ⟨cell⟩
  exact noBadPath2 ⟨Path2.singleton cell⟩

/-- Unrestricted step naturality, at universe zero. -/
def StepNat : Type 1 :=
  {A B : Type} → {f g : A → B} →
    (h : (x : A) → Step (f x) (g x)) → {x y : A} → (s : Step x y) →
    Step2 (Path.ap f (Path.lEmbed s) ++ₚ Path.lEmbed (h y))
      (Path.lEmbed (h x) ++ₚ Path.ap g (Path.lEmbed s))

theorem notStepNat : ¬ Nonempty StepNat := by
  intro ⟨nat⟩
  exact noBadStep2 ⟨nat (f := fun x => x) (g := fun x => x) badFamily testStep⟩

/-- Even allowing arbitrary finite pastings does not rescue unrestricted naturality. -/
def NatPath : Type 1 :=
  {A B : Type} → {f g : A → B} →
    (h : (x : A) → Path (f x) (g x)) → {x y : A} → (p : Path x y) →
    Path2 (Path.ap f p ++ₚ h y) (h x ++ₚ Path.ap g p)

theorem notNatPath : ¬ Nonempty NatPath := by
  intro ⟨nat⟩
  exact noBadPath2 ⟨nat (f := fun x => x) (g := fun x => x)
    (fun x => Path.lEmbed (badFamily x)) testPath⟩

end TDLC.Refutation
