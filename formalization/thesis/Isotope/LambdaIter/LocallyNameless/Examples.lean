import Isotope.LambdaIter.LocallyNameless.Equiv

namespace Isotope.LambdaIter.LocallyNameless.Examples

inductive Base | nat
inductive Instr | tick

instance instHasTy : HasTy Instr (Ty Base) where
  src _ := .base .nat
  trg _ := .base .nat

instance : HasEff Instr Unit where eff _ := ()

def Γ : Ctx String (Ty Base) := .snoc .nil (some "x") (.base .nat)
def β : BoundCtx (Ty Base) 0 := .nil

example : HasType Instr Γ β (.fv "x") (.base .nat) := .fv (by simp [Γ, Ctx.lookup])

def anonWk : FreeWk (.snoc Γ none Ty.unit) Γ where
  structural := .drop_none (.refl Γ)
  lookup x A h := ⟨A, by simpa [Ctx.lookup] using h, Subty.refl A⟩

example : HasType Instr (.snoc Γ none Ty.unit) β (.fv "x") (.base .nat) :=
  HasType.weaken anonWk .nil (Subty.refl _) (.fv (by simp [Γ, Ctx.lookup]))

example : HasType Instr Γ β (.let₁ (.fv "x") (.bv 0)) (.base .nat) :=
  .let₁ (A := .base .nat) (.fv (by simp [Γ, Ctx.lookup])) .bv

example : HasType Instr Γ β (.op .tick (.fv "x")) Ty.unit :=
  .sub (.op (.fv (show Γ.lookup "x" = some (instrSrc Instr.tick) from by rfl))) (.unit _)

end Isotope.LambdaIter.LocallyNameless.Examples
