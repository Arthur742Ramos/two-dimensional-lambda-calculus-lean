import Extensions

open TDLC.Syntax

-- Substitution under a binder must shift the substituted free variable.
example : subst (single (.var .zero : Tm [Ty.base] Ty.base))
    (.lam (.var (.succ .zero)) : Tm [Ty.base, Ty.base] (.arr Ty.base Ty.base)) =
    (.lam (.var (.succ .zero)) : Tm [Ty.base] (.arr Ty.base Ty.base)) := rfl

example : erase Example.source ≠ erase Example.target := by decide

example : Nonempty (HasType Example.Γ (erase Example.source) Ty.base) :=
  (representationAdequacy _ _ _).mpr ⟨_, rfl⟩

example : ¬ Nonempty TDLC.Refutation.StepNat := TDLC.Refutation.notStepNat
example : ¬ Nonempty TDLC.Refutation.NatPath := TDLC.Refutation.notNatPath

-- Both square boundaries are parallel but their group values differ.
example : TDLC.Refutation.dMul 4 3 = 1 := by decide
example : TDLC.Refutation.dMul 3 4 = 2 := by decide
