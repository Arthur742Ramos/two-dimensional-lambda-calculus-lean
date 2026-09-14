import Solution

/-! Standalone intrinsically typed de Bruijn syntax, capture-avoiding substitution,
and an evidence-preserving interpretation in the host-labelled calculus.
This module does not identify syntactically different beta/eta endpoints. -/

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
  induction h with
  | zero => rfl
  | succ h ih => exact congrArg Nat.succ ih

def eraseTyped : (t : Tm Γ a) → HasType Γ (erase t) a
  | .var v => .var v.lookup
  | .app f x => .app (eraseTyped f) (eraseTyped x)
  | .lam t => .lam (eraseTyped t)

def elaborate : HasType Γ r a → Tm Γ a
  | .var h => .var h.variable
  | .app f x => .app (elaborate f) (elaborate x)
  | .lam t => .lam (elaborate t)

theorem erase_elaborate (h : HasType Γ r a) : erase (elaborate h) = r := by
  induction h with
  | var h => exact congrArg Raw.var h.index_variable
  | app f x ihf ihx => simp only [elaborate, erase, ihf, ihx]
  | lam t ih => exact congrArg (Raw.lam _) ih

/-- Representation adequacy: exactly the extrinsically well-typed trees are represented. -/
theorem representationAdequacy (Γ : List Ty) (r : Raw) (a : Ty) :
    Nonempty (HasType Γ r a) ↔ ∃ t : Tm Γ a, erase t = r := by
  constructor
  · intro ⟨h⟩
    exact ⟨elaborate h, erase_elaborate h⟩
  · rintro ⟨t, rfl⟩
    exact ⟨eraseTyped t⟩

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
  have eq : @ρ = @σ := funext fun _ => funext fun v => h v
  cases eq
  rfl

theorem eval_rename (t : Tm Γ a) (r : Ren Γ Δ) (ρ : Env U Δ) :
    eval (rename r t) ρ = eval t (fun v => ρ (r v)) := by
  induction t generalizing Δ with
  | var v => rfl
  | app f x ihf ihx => simp only [rename, eval, ihf, ihx]
  | lam t ih =>
      funext x
      change eval (rename r.lift t) (ρ.extend x) = _
      rw [ih]
      apply eval_congr
      intro a v
      cases v <;> rfl

theorem eval_subst (t : Tm Γ a) (s : Sub Γ Δ) (ρ : Env U Δ) :
    eval (subst s t) ρ = eval t (fun v => eval (s v) ρ) := by
  induction t generalizing Δ with
  | var v => rfl
  | app f x ihf ihx => simp only [subst, eval, ihf, ihx]
  | lam t ih =>
      funext x
      change eval (subst s.lift t) (ρ.extend x) = _
      rw [ih]
      apply eval_congr
      intro a v
      cases v with
      | zero => rfl
      | succ v => exact eval_rename (s v) _ _

theorem eval_beta (t : Tm (a :: Γ) b) (x : Tm Γ a) (ρ : Env U Γ) :
    eval (subst (single x) t) ρ = eval t (ρ.extend (eval x ρ)) := by
  rw [eval_subst]
  apply eval_congr
  intro a v
  cases v <;> rfl

theorem eval_eta (f : Tm Γ (.arr a b)) (ρ : Env U Γ) :
    eval (etaExpand f) ρ = eval f ρ := by
  funext x
  change eval (rename (fun v => .succ v) f) (ρ.extend x) x = eval f ρ x
  rw [eval_rename]
  rfl

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
  cases hx
  cases hy
  rfl

theorem interpret_parity {t s : Tm Γ a} (c : Conv t s) (ρ : Env U Γ) :
    TDLC.Step.parity (interpret c ρ) = c.parity := by
  induction c with
  | beta t x => simp only [interpret, Conv.parity, parity_cast, TDLC.Step.parity]
  | eta f => simp only [interpret, Conv.parity, parity_cast, TDLC.Step.parity]
  | appLeft c x ih => exact ih ρ
  | appRight f c ih => exact ih ρ
  | lam c ih => rfl
  | refl t => rfl
  | sym c ih => exact ih ρ
  | trans c d ihc ihd =>
      change bxor _ _ = bxor _ _
      rw [ihc, ihd]

/-- Different grades reflect non-identification by the full host two-cell theory. -/
theorem noCell_of_parity_ne {t s : Tm Γ a} (c d : Conv t s)
    (hne : c.parity ≠ d.parity) (ρ : Env U Γ) :
    ¬ Nonempty (TDLC.Path2 (TDLC.Path.lEmbed (interpret c ρ))
      (TDLC.Path.lEmbed (interpret d ρ))) := by
  intro ⟨cells⟩
  have h := TDLC.path2PreservesParity cells
  rw [TDLC.Path.parity_lEmbed, TDLC.Path.parity_lEmbed,
    interpret_parity, interpret_parity] at h
  exact hne h

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
  intro h
  cases h

theorem routesDistinct : betaRoute ≠ etaRoute := by
  intro h
  have hp := congrArg Conv.parity h
  exact Bool.noConfusion hp

theorem interpretedRoutesSeparated (ρ : Env U Γ) :
    ¬ Nonempty (TDLC.Path2 (TDLC.Path.lEmbed (interpret betaRoute ρ))
      (TDLC.Path.lEmbed (interpret etaRoute ρ))) :=
  noCell_of_parity_ne betaRoute etaRoute (by decide) ρ

end Example

end TDLC.Syntax
