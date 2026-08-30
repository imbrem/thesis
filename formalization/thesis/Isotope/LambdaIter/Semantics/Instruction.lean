import Isotope.LambdaIter.Semantics.Model

/-!
# Models of primitive instructions

Typing and effects remain independent syntactic classes.  A semantic model
supplies a Kleisli interpretation for every instruction, and additionally a
genuinely pure interpretation when its effect is bottom.  The compatibility
law avoids dependent case analysis on whether an effect equals bottom.
-/

namespace Isotope.LambdaIter.Semantics

universe u v w x

/-- Denotations of a typed, effect-annotated instruction signature. -/
class InstructionModel (Φ : Type u) (τ : Type v) (ε : Type w)
    (m : Type x → Type x) [TypeFormers τ] [Subtyping τ]
    [TypeModel.{v, x} τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε] [Pure m] where
  /-- Every instruction has an effectful/Kleisli denotation. -/
  denote (f : Φ) : TyDen (τ := τ) (instrSrc f) → m (TyDen (τ := τ) (instrTrg f))
  /-- A bottom-effect instruction also has an ordinary function denotation. -/
  denotePure (f : Φ) (hf : (instrEff f : ε) = (⊥ : ε)) :
    TyDen (τ := τ) (instrSrc f) → TyDen (τ := τ) (instrTrg f)
  /-- The two interpretations agree after embedding the pure one. -/
  denote_pure (f : Φ) (hf : (instrEff f : ε) = (⊥ : ε))
      (a : TyDen (τ := τ) (instrSrc f)) :
    denote f a = pure (denotePure f hf a)

def denoteInstr [TypeFormers τ] [Subtyping τ] [TypeModel τ]
    [HasTy Φ τ] [HasEff Φ ε] [Bot ε] [Pure m]
    [InstructionModel Φ τ ε m] (f : Φ) :
    TyDen (τ := τ) (instrSrc f) → m (TyDen (τ := τ) (instrTrg f)) :=
  InstructionModel.denote (Φ := Φ) (τ := τ) (ε := ε) (m := m) f

def denotePureInstr [TypeFormers τ] [Subtyping τ] [TypeModel τ]
    [HasTy Φ τ] [HasEff Φ ε] [Bot ε] [Pure m]
    [InstructionModel Φ τ ε m] (f : Φ) (hf : (instrEff f : ε) = (⊥ : ε)) :
    TyDen (τ := τ) (instrSrc f) → TyDen (τ := τ) (instrTrg f) :=
  InstructionModel.denotePure (Φ := Φ) (τ := τ) (ε := ε) (m := m) f hf

end Isotope.LambdaIter.Semantics
