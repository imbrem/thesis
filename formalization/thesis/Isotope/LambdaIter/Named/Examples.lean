/-
Copyright (c) 2026 Remu G. -/
import Isotope.LambdaIter.Named.Equiv

namespace Isotope.LambdaIter.Named

inductive Base where | nat
inductive Instr where | succ

abbrev exampleSig : Signature (Ty Base) where
  Op := Instr
  src _ := .base .nat
  trg _ := .base .nat
  pure _ := True

example : HasType exampleSig [(some "x", .base .nat)]
    (.op .succ (.var "x")) (.base .nat) :=
  .op (.var (by simp [Ctx.lookup]))

example : HasType exampleSig [(none, .unit), (some "x", .base .nat)]
    (.var "x") (.base .nat) :=
  .var (by simp [Ctx.lookup])

end Isotope.LambdaIter.Named
