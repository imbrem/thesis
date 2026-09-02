import Isotope.LambdaIter.Subtyping.Named.Equiv

namespace Isotope.LambdaIter.Subtyping.Named

open Isotope.LambdaIter.Named

inductive Base where | nat
inductive Instr where | succ

instance : HasTy Instr (Ty Base) where
  src _ := Ty.base Base.nat
  trg _ := Ty.base Base.nat

instance : HasEff Instr Bool where
  eff _ := false

@[simp] theorem instrSrc_succ : instrSrc Instr.succ = Ty.base Base.nat := rfl
@[simp] theorem instrTrg_succ : instrTrg Instr.succ = Ty.base Base.nat := rfl

example : HasType (Φ := Instr) (.snoc .nil (some "x") (Ty.base Base.nat))
    (.op .succ (.var "x")) (Ty.base Base.nat) :=
  .op ⟨by simpa using Subty.refl (Ty.base Base.nat),
    by simpa using Subty.refl (Ty.base Base.nat)⟩ (.var (by simp [Ctx.lookup]))

example : HasType (Φ := Instr)
    (.snoc (.snoc .nil none Ty.unit) (some "x") (Ty.base Base.nat))
    (.var "x") (Ty.base Base.nat) :=
  .var (by simp [Ctx.lookup])

/-- Empty input is accepted contravariantly and any result can be viewed at
the terminal type, exactly as in the thesis instruction rule. -/
example : HasType (Φ := Instr)
    (.snoc (.nil : Ctx String (Ty Base)) (some "impossible") Ty.empty)
    (.op .succ (.abort (.var "impossible"))) Ty.unit := by
  apply HasType.op ⟨Subty.empty _, Subty.unit _⟩
  apply HasType.abort
  simpa using (HasType.var (Φ := Instr)
    (Γ := .snoc .nil (some "impossible") Ty.empty) (A := Ty.empty)
    (by simp [Ctx.lookup]))

end Isotope.LambdaIter.Subtyping.Named
