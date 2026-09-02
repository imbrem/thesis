import Isotope.LambdaSSA.Named.Typing
import Isotope.LambdaSSA.LocallyNameless.Typing
import Isotope.LambdaIter.Named.ToLocallyNameless

/-! # Translation from named to locally nameless lambda-SSA -/

namespace Isotope.LambdaSSA.Named.ToLocallyNameless

abbrev Scope := LambdaIter.Named.ToLocallyNameless.Scope

namespace Scope

/-- Push simultaneous binders in increasing index order, so binder `i`
resolves to de Bruijn index `i`. -/
def pushAll : {n : Nat} → (Fin n → Named.Binder ν) → Scope ν k → Scope ν (n + k)
  | 0, _, ρ => by simpa using ρ
  | n + 1, xs, ρ =>
      by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        LambdaIter.Named.ToLocallyNameless.Scope.push
          (xs 0) (pushAll (fun i => xs i.succ) ρ)

end Scope

/-- Translate a named expression relative to its enclosing value binders. -/
def translateTm [DecidableEq ν] (ρ : Scope ν n) :
    Named.Tm ν Φ → LocallyNameless.Tm ν Φ n
  | .var x => match ρ.resolve x with
    | .inl i => .bv i
    | .inr x => .fv x
  | .op f a => .op f (translateTm ρ a)
  | .let₁ x a b => .let₁ (translateTm ρ a) (translateTm (.push x ρ) b)
  | .pair a b => .pair (translateTm ρ a) (translateTm ρ b)
  | .unit => .unit
  | .let₂ x y a b => .let₂ (translateTm ρ a) (translateTm (.push y (.push x ρ)) b)
  | .inl a => .inl (translateTm ρ a)
  | .inr a => .inr (translateTm ρ a)
  | .case e x l y r =>
      .case (translateTm ρ e) (translateTm (.push x ρ) l) (translateTm (.push y ρ) r)
  | .abort a => .abort (translateTm ρ a)

/-- Translate a named region relative to independent value and label scopes. -/
def translateRegion [DecidableEq ν] [DecidableEq κ]
    (ρ : Scope ν n) (ls : Scope κ l) :
    Named.Region ν κ Φ → LocallyNameless.Region ν κ Φ n l
  | .br label arg => .br (ls.resolve label) (translateTm ρ arg)
  | .case discr x left y right =>
      .case (translateTm ρ discr)
        (translateRegion (.push x ρ) ls left)
        (translateRegion (.push y ρ) ls right)
  | .let₁ x value body =>
      .let₁ (translateTm ρ value) (translateRegion (.push x ρ) ls body)
  | .let₂ x y value body =>
      .let₂ (translateTm ρ value) (translateRegion (.push y (.push x ρ)) ls body)
  | .cfg entry arity labels params blocks =>
      let ls' := Scope.pushAll labels ls
      .cfg arity (translateRegion ρ ls' entry)
        (fun i => translateRegion (.push (params i) ρ) ls' (blocks i))

def translateTmClosed [DecidableEq ν] (t : Named.Tm ν Φ) :
    LocallyNameless.Tm ν Φ 0 := translateTm .nil t

def translateRegionClosed [DecidableEq ν] [DecidableEq κ]
    (r : Named.Region ν κ Φ) : LocallyNameless.Region ν κ Φ 0 0 :=
  translateRegion .nil .nil r

end Isotope.LambdaSSA.Named.ToLocallyNameless
