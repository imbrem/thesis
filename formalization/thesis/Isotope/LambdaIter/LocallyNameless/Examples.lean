import Isotope.LambdaIter.LocallyNameless.Equiv

namespace Isotope.LambdaIter.LocallyNameless.Examples

inductive Base | nat
inductive Instr | tick

def sig : Signature (Ty Base) where
  Instr := Instr
  src _ := .base .nat
  trg _ := .base .nat

def Γ : Ctx String (Ty Base) := .snoc .nil (some "x") (.base .nat)
def β : BoundCtx (Ty Base) 0 := .nil

example : HasType sig Γ β (.fv "x") (.base .nat) := .fv (by simp [Γ, Ctx.lookup])

def anonWk : FreeWk (.snoc Γ none Ty.unit) Γ where
  structural := .drop_none (.refl Γ)
  lookup x A h := ⟨A, by simpa [Ctx.lookup] using h, Subty.refl A⟩

example : HasType sig (.snoc Γ none Ty.unit) β (.fv "x") (.base .nat) :=
  HasType.weaken anonWk .nil (Subty.refl _) (.fv (by simp [Γ, Ctx.lookup]))

example : HasType sig Γ β (.let₁ (.fv "x") (.bv 0)) (.base .nat) :=
  .let₁ (A := .base .nat) (.fv (by simp [Γ, Ctx.lookup])) .bv

def tickTy : InstTy sig .tick (.base .nat) Ty.unit where
  input := by
    change Ty.Subty (Ty.base Base.nat) (Ty.base Base.nat)
    exact .refl _
  output := .unit _

example : HasType sig Γ β (.op .tick (.fv "x")) Ty.unit :=
  .op tickTy (.fv (by simp [Γ, Ctx.lookup]))

end Isotope.LambdaIter.LocallyNameless.Examples
