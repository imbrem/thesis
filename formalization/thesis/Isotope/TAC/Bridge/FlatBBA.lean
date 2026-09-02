import Isotope.TAC.Bridge.LambdaSSA

namespace Isotope.TAC.Bridge

universe u

/-- Structural address in a lexical dominator tree. -/
abbrev BlockAddress := List Nat

/-- One node of a flat basic-block-with-arguments graph.  Successors are
explicit structural addresses; branch arguments remain lambda-SSA terms. -/
inductive FlatNode (Φ : Type u) where
  | br (target : Nat) (arg : LambdaSSA.Tm Φ)
  | case (discr : LambdaSSA.Tm Φ) (left right : BlockAddress)
  | let₁ (value : LambdaSSA.Tm Φ) (next : BlockAddress)
  | let₂ (value : LambdaSSA.Tm Φ) (next : BlockAddress)
  | where_ (entry : BlockAddress) (blocks : List BlockAddress)
  | block (body : LexicalBBA Φ)

structure FlatBBA (Φ : Type u) where
  entry : BlockAddress
  blocks : List (BlockAddress × FlatNode Φ)

namespace LexicalBBA

def flattenAt : LexicalBBA Φ → BlockAddress → List (BlockAddress × FlatNode Φ)
  | .br target arg, here => [(here, .br target arg)]
  | .case discr left right, here =>
      (here, .case discr (here ++ [0]) (here ++ [1])) ::
        flattenAt left (here ++ [0]) ++ flattenAt right (here ++ [1])
  | .let₁ value body, here =>
      (here, .let₁ value (here ++ [0])) :: flattenAt body (here ++ [0])
  | .let₂ value body, here =>
      (here, .let₂ value (here ++ [0])) :: flattenAt body (here ++ [0])
  | .where_ entry arity blocks, here =>
      let entryAddress := here ++ [0]
      let blockAddress := fun i : Fin arity => here ++ [i.val + 1]
      (here, .where_ entryAddress (List.ofFn blockAddress)) ::
        flattenAt entry entryAddress ++
          List.ofFn (fun i => (blockAddress i, .block (blocks i)))
termination_by r _ => sizeOf r

def flatten (r : LexicalBBA Φ) : FlatBBA Φ where
  entry := []
  blocks := r.flattenAt []

@[simp] theorem flatten_entry (r : LexicalBBA Φ) : r.flatten.entry = [] := rfl

theorem flatten_blocks_finite (r : LexicalBBA Φ) :
    ∃ n, r.flatten.blocks.length = n := ⟨_, rfl⟩

end LexicalBBA
end Isotope.TAC.Bridge
