import Isotope.LambdaIter.Named.Equiv

namespace Isotope.LambdaIter.Named

inductive Base where | nat
inductive Instr where | succ

abbrev exampleSig : Signature (Ty Base) where
  Op := Instr
  src _ := .base .nat
  trg _ := .base .nat
  pure _ := True

example : HasType exampleSig (.snoc .nil (some "x") (.base .nat))
    (.op .succ (.var "x")) (.base .nat) :=
  .op ⟨Subty.refl _, Subty.refl _⟩ (.var (by simp [Ctx.lookup]))

example : HasType exampleSig (.snoc (.snoc .nil none .unit) (some "x") (.base .nat))
    (.var "x") (.base .nat) :=
  .var (by simp [Ctx.lookup])

/-- Empty input is accepted contravariantly and any result can be viewed at
the terminal type, exactly as in the thesis instruction rule. -/
example : HasType exampleSig (.snoc (.nil : Ctx String (Ty Base)) (some "impossible") .empty)
    (.op .succ (.abort (.var "impossible"))) .unit := by
  apply HasType.op ⟨Subty.empty _, Subty.unit _⟩
  apply HasType.abort
  simpa using (HasType.var (S := exampleSig)
    (Γ := .snoc .nil (some "impossible") .empty) (A := (.empty : Ty Base))
    (by simp [Ctx.lookup]))

end Isotope.LambdaIter.Named
