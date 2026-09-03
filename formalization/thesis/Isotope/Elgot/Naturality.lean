import Isotope.Elgot.Kleisli

/-! # Pointwise forms of complete-Elgot naturality -/

namespace Isotope.Elgot

universe u

variable {m : Type u → Type u} [Monad m] [LawfulMonad m]
variable [Iterate m] [LawfulElgotMonad m]
variable {A B C : Type u}

/-- Pointwise naturality, expanded into monadic notation.  This is the form
needed when contracting a CFG whose exit block runs a continuation while its
back edge resumes the same loop. -/
theorem iter_bind (f : A → m (B ⊕ A)) (g : B → m C) (a : A) :
    iter f a >>= g = iter (mapReturn f g) a := by
  simpa [kcomp] using
    congrFun (LawfulElgotMonad.naturality f g) a

/-- Naturality specialized to a pure result map. -/
theorem iter_map (f : A → m (B ⊕ A)) (g : B → C) (a : A) :
    (iter f a >>= fun b => pure (g b)) =
      iter (fun x => f x >>= fun step => pure (Sum.map g id step)) a := by
  rw [iter_bind]
  apply congrArg (fun body => iter body a)
  funext x
  unfold mapReturn
  apply bind_congr
  intro step
  cases step <;> simp [Function.comp_def]

end Isotope.Elgot
