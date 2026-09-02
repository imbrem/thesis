import Isotope.LambdaSSA.Syntax

/-! # Concrete lexical BBA bridge to lambda-SSA -/

namespace Isotope.TAC.Bridge

universe u

/-- Lexically organized basic-block syntax: branches and cases form control
flow, lets bind SSA values, and `where_` binds a finite family of dominated
blocks around an entry region. -/
inductive LexicalBBA (Φ : Type u) where
  | br (label : Nat) (arg : LambdaSSA.Tm Φ)
  | case (discr : LambdaSSA.Tm Φ) (left right : LexicalBBA Φ)
  | let₁ (value : LambdaSSA.Tm Φ) (body : LexicalBBA Φ)
  | let₂ (value : LambdaSSA.Tm Φ) (body : LexicalBBA Φ)
  | where_ (entry : LexicalBBA Φ) (arity : Nat)
      (blocks : Fin arity → LexicalBBA Φ)

namespace LexicalBBA

def toLambdaSSA : LexicalBBA Φ → LambdaSSA.Region Φ
  | .br label arg => .br label arg
  | .case discr left right => .case discr left.toLambdaSSA right.toLambdaSSA
  | .let₁ value body => .let₁ value body.toLambdaSSA
  | .let₂ value body => .let₂ value body.toLambdaSSA
  | .where_ entry arity blocks =>
      .cfg entry.toLambdaSSA arity (fun i => (blocks i).toLambdaSSA)

def ofLambdaSSA : LambdaSSA.Region Φ → LexicalBBA Φ
  | .br label arg => .br label arg
  | .case discr left right => .case discr (ofLambdaSSA left) (ofLambdaSSA right)
  | .let₁ value body => .let₁ value (ofLambdaSSA body)
  | .let₂ value body => .let₂ value (ofLambdaSSA body)
  | .cfg entry arity blocks =>
      .where_ (ofLambdaSSA entry) arity (fun i => ofLambdaSSA (blocks i))

@[simp] theorem of_to (r : LexicalBBA Φ) : ofLambdaSSA r.toLambdaSSA = r := by
  induction r with
  | br => rfl
  | case _ _ _ il ir => simp [toLambdaSSA, ofLambdaSSA, il, ir]
  | let₁ _ _ ih => simp [toLambdaSSA, ofLambdaSSA, ih]
  | let₂ _ _ ih => simp [toLambdaSSA, ofLambdaSSA, ih]
  | where_ _ _ _ ie ib =>
      simp only [toLambdaSSA, ofLambdaSSA, ie]
      congr
      funext i
      exact ib i

@[simp] theorem to_of (r : LambdaSSA.Region Φ) : toLambdaSSA (ofLambdaSSA r) = r := by
  induction r with
  | br => rfl
  | case _ _ _ il ir => simp [toLambdaSSA, ofLambdaSSA, il, ir]
  | let₁ _ _ ih => simp [toLambdaSSA, ofLambdaSSA, ih]
  | let₂ _ _ ih => simp [toLambdaSSA, ofLambdaSSA, ih]
  | cfg _ _ _ ie ib =>
      simp only [toLambdaSSA, ofLambdaSSA, ie]
      congr
      funext i
      exact ib i

/-- The dedicated lexical BBA syntax is concretely equivalent to the current
de Bruijn lambda-SSA region syntax. -/
def equivalence : LexicalBBA Φ ≃ LambdaSSA.Region Φ where
  toFun := toLambdaSSA
  invFun := ofLambdaSSA
  left_inv := of_to
  right_inv := to_of

end LexicalBBA
end Isotope.TAC.Bridge
