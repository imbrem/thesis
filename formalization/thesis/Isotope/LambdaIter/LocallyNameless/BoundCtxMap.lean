import Isotope.LambdaIter.LocallyNameless.Context

/-!
# The functorial action of a map of type universes on bound contexts

A signature morphism acts on types; a bound context is a length-indexed list
of types, so it acts on bound contexts too.  This file supplies that action
and the three facts every downstream cast needs: how it interacts with
lookup, that it is functorial, and that it preserves `snoc` on the nose (the
last is definitional, which is what keeps the reindexing casts confined to
the `Fin`-lookup and type-former positions).

## Shared-namespace note

`BoundCtx.map` and its lemmas live in the shared namespace
`Isotope.LambdaIter.LocallyNameless.BoundCtx`.
-/

namespace Isotope.LambdaIter.LocallyNameless

namespace BoundCtx

universe u v w

variable {τ : Type u} {σ : Type v} {n : Nat}

/-- Apply a map of type universes to every slot of a bound context. -/
def map (f : τ → σ) : {n : Nat} → BoundCtx τ n → BoundCtx σ n
  | 0, .nil => .nil
  | _ + 1, .snoc Γ A => .snoc (map f Γ) (f A)

@[simp] theorem map_nil (f : τ → σ) : map f (.nil : BoundCtx τ 0) = .nil := rfl

/-- `map` preserves `snoc` definitionally.  Every binder-introducing operation
of a model therefore needs no transport. -/
@[simp] theorem map_snoc (f : τ → σ) (Γ : BoundCtx τ n) (A : τ) :
    map f (Γ.snoc A) = (map f Γ).snoc (f A) := rfl

/-- Lookup commutes with the action.  This is *not* definitional (`get` is by
`Fin.cases`), and it is the source of the transport in the `var` clause of a
reindexed model. -/
@[simp] theorem map_get (f : τ → σ) :
    ∀ {n : Nat} (Γ : BoundCtx τ n) (i : Fin n), (map f Γ).get i = f (Γ.get i)
  | 0, .nil, i => Fin.elim0 i
  | _ + 1, .snoc Γ A, i => by
      refine Fin.cases rfl (fun j => ?_) i
      simpa [get] using map_get f Γ j

/-- The action of the identity is the identity. -/
@[simp] theorem map_id : ∀ {n : Nat} (Γ : BoundCtx τ n), map id Γ = Γ
  | 0, .nil => rfl
  | _ + 1, .snoc Γ A => by rw [map_snoc, map_id Γ]; rfl

/-- The action of a composite is the composite of the actions. -/
theorem map_comp {ρ : Type w} (f : τ → σ) (g : σ → ρ) :
    ∀ {n : Nat} (Γ : BoundCtx τ n), map (g ∘ f) Γ = map g (map f Γ)
  | 0, .nil => rfl
  | _ + 1, .snoc Γ A => by rw [map_snoc, map_snoc, map_snoc, map_comp f g Γ]; rfl

/-- The action agrees with the `Fin`-function view of a bound context. -/
theorem get_map (f : τ → σ) (Γ : BoundCtx τ n) : (map f Γ).get = f ∘ Γ.get :=
  funext fun i => map_get f Γ i

end BoundCtx

end Isotope.LambdaIter.LocallyNameless
