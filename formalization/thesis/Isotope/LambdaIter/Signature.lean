import Isotope.LambdaIter.Ty

/-!
# Instruction signatures

Instruction typing and effects are independent interfaces. Raw terms need
neither: they are parameterized directly by their instruction type `Φ`.
-/

namespace Isotope.LambdaIter

/-- Source and target types of primitive instructions. -/
class HasTy (Φ : Type u) (τ : Type v) where
  src : Φ → τ
  trg : Φ → τ

/-- Effect annotation of primitive instructions. -/
class HasEff (Φ : Type u) (ε : Type v) where
  eff : Φ → ε

/-- Convenience bundle when both instruction typing and effects are needed. -/
class Signature (Φ : Type u) (τ : Type v) (ε : Type w)
    extends HasTy Φ τ, HasEff Φ ε

def instrSrc [HasTy Φ τ] (f : Φ) : τ := HasTy.src f
def instrTrg [HasTy Φ τ] (f : Φ) : τ := HasTy.trg f
def instrEff [HasEff Φ ε] (f : Φ) : ε := HasEff.eff f

/-- Purity relative to an explicitly supplied pure effect. -/
def IsPure [HasEff Φ ε] (pureEff : ε) (f : Φ) : Prop := instrEff f = pureEff

section Examples

variable [HasTy Φ τ] [HasEff Φ ε] (f : Φ) (pureEff : ε)

example : τ := instrSrc f
example : τ := instrTrg f
example : ε := instrEff f
example : Prop := IsPure pureEff f

end Examples

end Isotope.LambdaIter
