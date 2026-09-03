import Isotope.LambdaIter.Models.Categorical.Alg
import Isotope.LambdaIter.Models.Initial

/-!
# Initiality into a Freyd-categorical model

`Models/Initial.lean` states initiality of the quotiented syntax in the
category of algebras, and its honest boundary says the statement "is **not** a
Freyd or Elgot category, and nothing here proves that a Freyd category yields
one".  `Models/Categorical/Alg.lean` now proves exactly that, so initiality
applies to Freyd-categorical models: from the quotiented syntax into any
strong Elgot Freyd category with an interpretation of the signature satisfying
the two coherence classes there is exactly one morphism of algebras, and it
sends the class of a derivation to its categorical denotation.
-/

namespace Isotope.LambdaIter.Categorical

open LocallyNameless
open CategoryTheory CategoryTheory.Limits
open Isotope.LambdaIter.Subtyping.Semantics.Categorical

universe u v₁ u₁ u₂

variable {S : Sig.{u}} [Subtyping S.Ty]
variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{u} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C]
  (J : Functor V C) [StrongElgotFreydCategory J]
  (M : TypeModel S.Ty V) [InstructionModel J M S.Instr]
  [LocallyNameless.Categorical.TypingCoherent (τ := S.Ty) (ν := Empty)
    (Φ := S.Instr) J M]
  [LocallyNameless.Categorical.LawfulModel (τ := S.Ty) (ν := Empty)
    (Φ := S.Instr) (ε := S.Eff) (pureEff := S.pureEff) J M]

/-- **Initiality into a Freyd-categorical model.**  There is exactly one
morphism of algebras from the quotiented syntax into the algebra of a strong
Elgot Freyd model of the signature. -/
noncomputable instance uniqueHomCategorical :
    Unique (Syn.{u} S ⟶ Alg.ofCategorical J M) :=
  Syn.uniqueHom _

/-- The unique morphism sends the class of a derivation to its categorical
denotation. -/
@[simp] theorem toHom_ofCategorical_mk {n : Nat} {β : BoundCtx S.Ty n}
    {t : Tm Empty S.Instr n} {A : S.Ty}
    (h : HasType S.Instr Ctx.nil β t A) :
    (Syn.toHom (Alg.ofCategorical J M)).map (Syn.mk h) =
      LocallyNameless.Categorical.denote J M h := by
  rw [Syn.toHom_map, Syn.interp_mk]
  exact ofCategorical_denote J M h

end Isotope.LambdaIter.Categorical
