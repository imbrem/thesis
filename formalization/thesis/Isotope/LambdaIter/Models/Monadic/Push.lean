import Isotope.LambdaIter.Models.Monadic.Alg
import Isotope.Elgot.Morphism

/-!
# Pushing a monadic model along an Elgot morphism

`Alg.ofModel` turns a lawful Elgot monad with an interpretation of a signature
into an algebra of the lambda-iter presentation.  This file makes that
assignment *functorial in the monad*: an `ElgotHom m n` pushes a model in `m`
forward to a model in `n` with the same type interpretation, and induces a
morphism of algebras between the two.

## Why an `ElgotHom` and not a `MonadHom`

Ten of the twelve term formers only need `pure` and `>>=` to be preserved.
`iter` needs the third law, and there is no way around it: iteration is extra
algebraic structure on a monad, so a mere monad morphism transports the
sequential fragment of a model and nothing more.  (This is the same split the
bridge itself exhibits: lambda-case needs no `Iterate`, lambda-iter does.)

## The one piece of friction: environments

`SeqModel.Env` is defined by recursion on the bound context *using the model*,
so `M.Env β` and `(M.push φ).Env β` are not definitionally equal even though
the two models have the same `interp` field — the recursion cannot unfold at a
variable context.  `Env.toPush` and `Env.ofPush` are the two evident
structural bijections, and they are mutually inverse, commute with `get`, and
send a `snoc` to a `snoc` *by `rfl`*, which is what keeps the twelve
homomorphism proofs one-liners.

The pushforward is factored through `Model.reinterpret`, which replaces only
the instruction denotations.  Keeping that separate is what lets two
pushforwards along *different* morphisms be compared: they are equal as soon
as their instruction denotations are (`push_congr`).
-/

namespace Isotope.LambdaIter

open LocallyNameless
open Isotope.Elgot
open Isotope.LambdaIter.Monadic
open Isotope.LambdaIter.Monadic.SeqModel

universe u v

namespace Monadic

variable {S : Sig.{u}} {m n : Type v → Type v} [Monad m] [Monad n]

/-! ### Replacing the instruction denotations -/

/-- A model with its Kleisli instruction denotations replaced, possibly in a
different monad.  The type interpretation is unchanged, *definitionally*. -/
def Model.reinterpret (M : Model.{u, v} S m)
    (d : ∀ f : S.Instr, M.interp (instrSrc f) → n (M.interp (instrTrg f)))
    (hd : ∀ (f : S.Instr) (hf : IsPure S.pureEff f) (a : M.interp (instrSrc f)),
      d f a = pure (M.denotePureInstr f hf a)) :
    Model.{u, v} S n where
  interp := M.interp
  denoteInstr := d
  denotePureInstr := M.denotePureInstr
  denoteInstr_pure := hd
  tensorEquiv := M.tensorEquiv
  unitEquiv := M.unitEquiv
  coprodEquiv := M.coprodEquiv
  emptyEquiv := M.emptyEquiv

@[simp] theorem Model.reinterpret_interp (M : Model.{u, v} S m) {d hd} :
    (M.reinterpret (n := n) d hd).interp = M.interp := rfl

@[simp] theorem Model.reinterpret_denoteInstr (M : Model.{u, v} S m) {d hd} :
    (M.reinterpret (n := n) d hd).denoteInstr = d := rfl

/-- Two reinterpretations with the same instruction denotations are equal.
The purity coherence field is a proposition, so it contributes nothing. -/
theorem Model.reinterpret_congr (M : Model.{u, v} S m)
    {d d' : ∀ f : S.Instr, M.interp (instrSrc f) → n (M.interp (instrTrg f))}
    {hd hd'} (h : d = d') : M.reinterpret d hd = M.reinterpret d' hd' := by
  subst h; rfl

/-- The pushforward of a model along a monad morphism: interpret each
instruction in `m` and then transport into `n`. -/
def Model.push (M : Model.{u, v} S m) (φ : MonadHom m n) : Model.{u, v} S n :=
  M.reinterpret (fun f a => φ.app (M.denoteInstr f a))
    (fun f hf a => by
      show φ.app (M.denoteInstr f a) = _
      rw [M.denoteInstr_pure f hf a]
      exact φ.app_pure _)

@[simp] theorem Model.push_interp (M : Model.{u, v} S m) (φ : MonadHom m n) :
    (M.push φ).interp = M.interp := rfl

@[simp] theorem Model.push_tensorEquiv (M : Model.{u, v} S m) (φ : MonadHom m n) :
    (M.push φ).tensorEquiv = M.tensorEquiv := rfl

@[simp] theorem Model.push_unitEquiv (M : Model.{u, v} S m) (φ : MonadHom m n) :
    (M.push φ).unitEquiv = M.unitEquiv := rfl

@[simp] theorem Model.push_coprodEquiv (M : Model.{u, v} S m) (φ : MonadHom m n) :
    (M.push φ).coprodEquiv = M.coprodEquiv := rfl

@[simp] theorem Model.push_emptyEquiv (M : Model.{u, v} S m) (φ : MonadHom m n) :
    (M.push φ).emptyEquiv = M.emptyEquiv := rfl

@[simp] theorem Model.push_denoteInstr (M : Model.{u, v} S m) (φ : MonadHom m n)
    (f : S.Instr) (a : M.interp (instrSrc f)) :
    (M.push φ).denoteInstr f a = φ.app (M.denoteInstr f a) := rfl

/-- **Pushforwards along morphisms that agree on the instructions are equal.**
Over a signature with no instructions this makes *every* pushforward of a
fixed model the same model, which is what lets distinct morphisms be compared
as parallel arrows. -/
theorem Model.push_congr (M : Model.{u, v} S m) (φ ψ : MonadHom m n)
    (h : ∀ (f : S.Instr) (a : M.interp (instrSrc f)),
      φ.app (M.denoteInstr f a) = ψ.app (M.denoteInstr f a)) :
    M.push φ = M.push ψ :=
  M.reinterpret_congr (funext fun f => funext fun a => h f a)

/-! ### Transporting environments -/

namespace SeqModel.Env

variable (M : Model.{u, v} S m)
  (d : ∀ f : S.Instr, M.interp (instrSrc f) → n (M.interp (instrTrg f)))
  (hd : ∀ (f : S.Instr) (hf : IsPure S.pureEff f) (a : M.interp (instrSrc f)),
    d f a = pure (M.denotePureInstr f hf a))

/-- Read an environment of `M` as an environment of a reinterpretation of `M`.
No transport is needed: the two models have the same `interp` field. -/
def toReinterpret : {k : Nat} → {β : BoundCtx S.Ty k} →
    M.Env β → (M.reinterpret d hd).Env β
  | _, .nil, _ => PUnit.unit
  | _, .snoc _ _, ρ => (toReinterpret ρ.1, ρ.2)

/-- Read an environment of a reinterpretation of `M` as an environment of `M`. -/
def ofReinterpret : {k : Nat} → {β : BoundCtx S.Ty k} →
    (M.reinterpret d hd).Env β → M.Env β
  | _, .nil, _ => PUnit.unit
  | _, .snoc _ _, ρ => (ofReinterpret ρ.1, ρ.2)

@[simp] theorem ofReinterpret_snoc {k : Nat} {β : BoundCtx S.Ty k} {A : S.Ty}
    (ρ : (M.reinterpret d hd).Env β) (a : M.interp A) :
    ofReinterpret M d hd (β := .snoc β A) (ρ, a) = (ofReinterpret M d hd ρ, a) := rfl

@[simp] theorem toReinterpret_snoc {k : Nat} {β : BoundCtx S.Ty k} {A : S.Ty}
    (ρ : M.Env β) (a : M.interp A) :
    toReinterpret M d hd (β := .snoc β A) (ρ, a) = (toReinterpret M d hd ρ, a) := rfl

@[simp] theorem get_ofReinterpret : ∀ {k : Nat} {β : BoundCtx S.Ty k}
    (ρ : (M.reinterpret d hd).Env β) (i : Fin k),
    Env.get (ofReinterpret M d hd ρ) i = Env.get ρ i
  | _, .snoc β A, ρ, i => by
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · exact get_ofReinterpret ρ.1 j

@[simp] theorem get_toReinterpret : ∀ {k : Nat} {β : BoundCtx S.Ty k}
    (ρ : M.Env β) (i : Fin k),
    Env.get (toReinterpret M d hd ρ) i = Env.get ρ i
  | _, .snoc β A, ρ, i => by
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · exact get_toReinterpret ρ.1 j

@[simp] theorem ofReinterpret_toReinterpret : ∀ {k : Nat} {β : BoundCtx S.Ty k}
    (ρ : M.Env β), ofReinterpret M d hd (toReinterpret M d hd ρ) = ρ
  | _, .nil, _ => rfl
  | _, .snoc β A, ρ => by
      apply Prod.ext
      · exact ofReinterpret_toReinterpret ρ.1
      · rfl

@[simp] theorem toReinterpret_ofReinterpret : ∀ {k : Nat} {β : BoundCtx S.Ty k}
    (ρ : (M.reinterpret d hd).Env β), toReinterpret M d hd (ofReinterpret M d hd ρ) = ρ
  | _, .nil, _ => rfl
  | _, .snoc β A, ρ => by
      apply Prod.ext
      · exact toReinterpret_ofReinterpret ρ.1
      · rfl

end SeqModel.Env

/-- Read an environment of `M` as an environment of its pushforward. -/
abbrev SeqModel.Env.toPush (M : Model.{u, v} S m) (φ : MonadHom m n)
    {k : Nat} {β : BoundCtx S.Ty k} (ρ : M.Env β) : (M.push φ).Env β :=
  SeqModel.Env.toReinterpret M _ _ ρ

/-- Read an environment of the pushforward of `M` as an environment of `M`. -/
abbrev SeqModel.Env.ofPush (M : Model.{u, v} S m) (φ : MonadHom m n)
    {k : Nat} {β : BoundCtx S.Ty k} (ρ : (M.push φ).Env β) : M.Env β :=
  SeqModel.Env.ofReinterpret M _ _ ρ

/-! ### The induced morphism of algebras -/

section Hom

variable [LawfulMonad m] [LawfulMonad n] [Iterate m] [Iterate n]
variable [LawfulElgotMonad m] [LawfulElgotMonad n] [InjectiveFormers S.Ty]

open SeqModel.Env

/-- **An Elgot morphism of monads induces a morphism of algebras.**  Applying
`φ` to the denotation of a term is the denotation of that term in the
pushed-forward model, for all twelve term formers at once. -/
def Alg.homOfElgotHom (M : Model.{u, v} S m) (φ : ElgotHom m n) :
    Alg.ofModel M ⟶ Alg.ofModel (M.push φ.toMonadHom) where
  map x := fun ρ => φ.app (x (ofPush M φ.toMonadHom ρ))
  map_var i := by
    funext ρ
    show φ.app (pure (SeqModel.Env.get (ofPush M φ.toMonadHom ρ) _)) = _
    rw [φ.app_pure, get_ofReinterpret]
    rfl
  map_op f a := by
    funext ρ
    show φ.app (a _ >>= M.denoteInstr f) = φ.app (a _) >>= (M.push φ.toMonadHom).denoteInstr f
    rw [φ.app_bind]
    rfl
  map_let₁ a b := by
    funext ρ
    show φ.app (a _ >>= fun x => b (_, x)) = φ.app (a _) >>= fun x => φ.app (b (_, x))
    rw [φ.app_bind]
  map_unit := by
    intro k β
    funext ρ
    show φ.app (pure (M.unitEquiv.symm ())) = (pure (M.unitEquiv.symm ()) : n _)
    rw [φ.app_pure]
  map_pair a b := by
    funext ρ
    show φ.app (a _ >>= fun x => b _ >>= fun y => pure ((M.tensorEquiv _ _).symm (x, y))) = _
    rw [φ.app_bind]
    refine bind_congr fun x => ?_
    rw [φ.app_bind]
    exact bind_congr fun y => φ.app_pure _
  map_let₂ a c := by
    funext ρ
    show φ.app (a _ >>= fun ab => c ((_, (M.tensorEquiv _ _ ab).1), (M.tensorEquiv _ _ ab).2)) =
      φ.app (a _) >>= fun ab =>
        φ.app (c ((ofPush M φ.toMonadHom ρ, (M.tensorEquiv _ _ ab).1),
          (M.tensorEquiv _ _ ab).2))
    rw [φ.app_bind]
  map_inl a := by
    funext ρ
    show φ.app (a _ >>= fun x => pure ((M.coprodEquiv _ _).symm (.inl x))) = _
    rw [φ.app_bind]
    exact bind_congr fun x => φ.app_pure _
  map_inr b := by
    funext ρ
    show φ.app (b _ >>= fun x => pure ((M.coprodEquiv _ _).symm (.inr x))) = _
    rw [φ.app_bind]
    exact bind_congr fun x => φ.app_pure _
  map_case e l r := by
    funext ρ
    simp only [Alg.ofModel, ops, Model.push_coprodEquiv]
    refine (φ.app_bind _ _).trans (bind_congr fun x => ?_)
    cases M.coprodEquiv _ _ x <;> rfl
  map_abort a := by
    funext ρ
    show φ.app (a _ >>= fun z => Empty.elim (M.emptyEquiv z)) = _
    rw [φ.app_bind]
    exact bind_congr fun z => (M.emptyEquiv z).elim
  map_iter a b := by
    funext ρ
    show φ.app (a _ >>= Elgot.iter fun x =>
      b (_, x) >>= fun s => pure (M.coprodEquiv _ _ s)) = _
    rw [φ.app_bind]
    refine bind_congr fun x => ?_
    rw [φ.app_iter]
    refine congrFun (congrArg Elgot.iter (funext fun y => ?_)) x
    rw [φ.app_bind]
    exact bind_congr fun s => φ.app_pure _

@[simp] theorem Alg.homOfElgotHom_map (M : Model.{u, v} S m) (φ : ElgotHom m n)
    {k : Nat} {β : BoundCtx S.Ty k} {A : S.Ty} (x : (Alg.ofModel M).El β A) :
    (Alg.homOfElgotHom M φ).map x = fun ρ => φ.app (x (ofPush M φ.toMonadHom ρ)) := rfl

/-- **The pushed-forward denotation is the transported denotation.**  This is
`Alg.Hom.map_denote` for `homOfElgotHom`, spelled out for the monadic
denotation: it says that computing in `n` after transporting agrees with
transporting after computing in `m`. -/
theorem denote_push (M : Model.{u, v} S m) (φ : ElgotHom m n)
    {k : Nat} {β : BoundCtx S.Ty k} {t : Tm Empty S.Instr k} {A : S.Ty}
    (h : HasType S.Instr Ctx.nil β t A) (ρ : M.Env β) :
    denote (M.push φ.toMonadHom) h (toPush M φ.toMonadHom ρ) = φ.app (denote M h ρ) := by
  have := congrFun ((Alg.homOfElgotHom M φ).map_denote h) (toPush M φ.toMonadHom ρ)
  rw [Alg.homOfElgotHom_map] at this
  simp only [ofModel_denote, SeqModel.Env.ofReinterpret_toReinterpret] at this
  exact this.symm

end Hom

end Monadic

end Isotope.LambdaIter
