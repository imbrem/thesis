import Isotope.LambdaIter.Models.Monadic.Coherence

/-!
# Soundness of the lambda-iter equational theory

One lemma per axiom of `Eqv`, in the shape the axiom rule produces after the
given derivations have been normalised by coherence.  The structural and
sequencing axioms are the lambda-case lemmas verbatim; the four iteration
axioms are where `LawfulElgotMonad` is used, one law each — fixpoint,
naturality, codiagonal, and (for the `uniformity` rule of `Eqv`) uniformity.

Two lemmas are stated *across* types, because for those axioms the two sides'
derivations need not agree on an intermediate type: `sound_unitEta` (the
scrutinee of a discarding `let` can be typed at anything) and
`sound_emptyInitial` (likewise for an `abort`).  Both go through the coupling
of `Monadic/Coupling.lean`.
-/

namespace Isotope.LambdaIter.Monadic

open LocallyNameless

open Isotope.Elgot
open Isotope.LambdaIter.Monadic.SeqModel

universe u v

variable {S : Sig.{u}} {m : Type v → Type v} [Monad m] [LawfulMonad m]
variable [Iterate m]

section Axioms

variable (M : Model.{u, v} S m) {n : Nat} {β : BoundCtx S.Ty n}

/-- Soundness of the beta law for `let`. -/
theorem sound_letBeta {a : Tm Empty S.Instr n} {b : Tm Empty S.Instr (n + 1)}
    {A B : S.Ty} (hp : Pure S.pureEff a)
    (ha : HasType S.Instr Ctx.nil β a A)
    (hb : HasType S.Instr Ctx.nil (.snoc β A) b B) (ρ : M.Env β) :
    denote M (.let₁ ha hb) ρ = denote M (hb.instantiate ha) ρ := by
  obtain ⟨x, hx⟩ := denote_pure_factor M hp ha ρ
  rw [denote_let₁, hx, pure_bind, denote_instantiate M hb ha ρ x hx]

/-- Soundness of the eta law for `let`. -/
theorem sound_letEta {a : Tm Empty S.Instr n} {A : S.Ty}
    (ha : HasType S.Instr Ctx.nil β a A) (ρ : M.Env β) :
    denote M (.let₁ ha HasType.newest) ρ = denote M ha ρ := by
  rw [denote_let₁]
  simp only [denote_newest]
  exact bind_pure _

/-- Soundness of the eta law for the unit type.  The discarded scrutinee may be
typed at anything on the left, so this lemma too is stated across types, and
goes through the coupling. -/
theorem sound_unitEta [LawfulElgotMonad m] [InjectiveFormers S.Ty] {a : Tm Empty S.Instr n} {A : S.Ty}
    (h₁ : HasType S.Instr Ctx.nil β a A)
    (ha : HasType S.Instr Ctx.nil β a unit) (ρ : M.Env β) :
    denote M (.let₁ h₁ .unit) ρ = denote M ha ρ := by
  rw [denote_let₁, ← bind_pure (denote M ha ρ)]
  refine Coupled.bind_eq (denote_coupled M h₁ ha ρ ρ (EnvRel.refl' ρ)) ?_
  intro p
  rw [denote_unit]
  have hu : (M.unitEquiv.symm () : M.interp unit) = p.val.2 :=
    M.unitEquiv.injective (Subsingleton.elim _ _)
  rw [hu]
  exact Coupled.refl' _

/-- Soundness of the beta law for pairs. -/
theorem sound_pairBeta {a b : Tm Empty S.Instr n} {c : Tm Empty S.Instr (n + 2)}
    {A B C : S.Ty} (ha : HasType S.Instr Ctx.nil β a A)
    (hb : HasType S.Instr Ctx.nil β b B)
    (hc : HasType S.Instr Ctx.nil ((β.snoc A).snoc B) c C)
    (ρ : M.Env β) :
    denote M (.let₂ (.pair ha hb) hc) ρ =
      denote M (.let₁ ha (.let₁ (hb.lift (B := A)) hc)) ρ := by
  simp only [denote_let₂, denote_pair, denote_let₁, bind_assoc]
  refine bind_congr fun x => ?_
  rw [denote_lift]
  refine bind_congr fun y => ?_
  rw [pure_bind]
  simp

/-- Soundness of the eta law for pairs. -/
theorem sound_pairEta {a : Tm Empty S.Instr n} {A B : S.Ty}
    (ha : HasType S.Instr Ctx.nil β a (tensor A B))
    (ρ : M.Env β) :
    denote M (.let₂ ha (.pair HasType.previous HasType.newest)) ρ =
      denote M ha ρ := by
  simp only [denote_let₂, denote_pair, denote_previous, denote_newest,
    pure_bind]
  calc
    _ = denote M ha ρ >>= pure :=
      bind_congr fun ab => by simp
    _ = _ := bind_pure _

/-- Soundness of the left beta law for `case`. -/
theorem sound_caseBetaL {e : Tm Empty S.Instr n} {l r : Tm Empty S.Instr (n + 1)}
    {A B C : S.Ty} (he : HasType S.Instr Ctx.nil β e A)
    (hl : HasType S.Instr Ctx.nil (.snoc β A) l C)
    (hr : HasType S.Instr Ctx.nil (.snoc β B) r C) (ρ : M.Env β) :
    denote M (.case (.inl (B := B) he) hl hr) ρ = denote M (.let₁ he hl) ρ := by
  simp only [denote_case, denote_inl, denote_let₁, bind_assoc, pure_bind]
  exact bind_congr fun x => by rw [Equiv.apply_symm_apply]

/-- Soundness of the right beta law for `case`. -/
theorem sound_caseBetaR {e : Tm Empty S.Instr n} {l r : Tm Empty S.Instr (n + 1)}
    {A B C : S.Ty} (he : HasType S.Instr Ctx.nil β e B)
    (hl : HasType S.Instr Ctx.nil (.snoc β A) l C)
    (hr : HasType S.Instr Ctx.nil (.snoc β B) r C) (ρ : M.Env β) :
    denote M (.case (.inr (A := A) he) hl hr) ρ = denote M (.let₁ he hr) ρ := by
  simp only [denote_case, denote_inr, denote_let₁, bind_assoc, pure_bind]
  exact bind_congr fun x => by rw [Equiv.apply_symm_apply]

/-- Soundness of the eta law for `case`. -/
theorem sound_caseEta {e : Tm Empty S.Instr n} {A B : S.Ty}
    (he : HasType S.Instr Ctx.nil β e (coprod A B))
    (ρ : M.Env β) :
    denote M (.case he (.inl HasType.newest) (.inr HasType.newest)) ρ =
      denote M he ρ := by
  calc
    _ = denote M he ρ >>= pure := by
        rw [denote_case]
        refine bind_congr fun x => ?_
        cases hs : M.coprodEquiv A B x with
        | inl a =>
            simp only [denote_inl, denote_newest, pure_bind]
            exact congrArg (fun z => (Pure.pure z : m (M.interp _)))
              (by simpa [hs] using (M.coprodEquiv A B).symm_apply_apply x)
        | inr b =>
            simp only [denote_inr, denote_newest, pure_bind]
            exact congrArg (fun z => (Pure.pure z : m (M.interp _)))
              (by simpa [hs] using (M.coprodEquiv A B).symm_apply_apply x)
    _ = _ := bind_pure _

/-- Soundness of the instruction-sequencing law. -/
theorem sound_bindOp {f : S.Instr} {a : Tm Empty S.Instr n}
    {c : Tm Empty S.Instr (n + 1)} {C : S.Ty}
    (ha : HasType S.Instr Ctx.nil β a (instrSrc f))
    (hc : HasType S.Instr Ctx.nil (.snoc β (instrTrg f)) c C)
    (ρ : M.Env β) :
    denote M (.let₁ (.op ha) hc) ρ =
      denote M (.let₁ ha (.let₁ (.op HasType.newest) hc.underBinder)) ρ := by
  simp only [denote_let₁, denote_op, denote_newest, pure_bind, bind_assoc,
    denote_underBinder]

/-- Soundness of the associativity law for `let`. -/
theorem sound_bindLet {a : Tm Empty S.Instr n} {b c : Tm Empty S.Instr (n + 1)}
    {A B C : S.Ty} (ha : HasType S.Instr Ctx.nil β a A)
    (hb : HasType S.Instr Ctx.nil (.snoc β A) b B)
    (hc : HasType S.Instr Ctx.nil (.snoc β B) c C) (ρ : M.Env β) :
    denote M (.let₁ (.let₁ ha hb) hc) ρ =
      denote M (.let₁ ha (.let₁ hb hc.underBinder)) ρ := by
  simp only [denote_let₁, bind_assoc, denote_underBinder]

/-- Soundness of the commuting conversion for a `let` over a pair split. -/
theorem sound_bindLetPair {e : Tm Empty S.Instr n} {c : Tm Empty S.Instr (n + 2)}
    {d : Tm Empty S.Instr (n + 1)} {A B C D : S.Ty}
    (he : HasType S.Instr Ctx.nil β e (tensor A B))
    (hc : HasType S.Instr Ctx.nil ((β.snoc A).snoc B) c C)
    (hd : HasType S.Instr Ctx.nil (.snoc β C) d D) (ρ : M.Env β) :
    denote M (.let₁ (.let₂ he hc) hd) ρ =
      denote M (.let₂ he (.let₁ hc (hd.underBinder.underBinder))) ρ := by
  simp only [denote_let₁, denote_let₂, bind_assoc, denote_underBinder]

/-- Soundness of the commuting conversion for a `let` over a `case`. -/
theorem sound_bindLetCase {e : Tm Empty S.Instr n}
    {l r d : Tm Empty S.Instr (n + 1)} {A B C D : S.Ty}
    (he : HasType S.Instr Ctx.nil β e (coprod A B))
    (hl : HasType S.Instr Ctx.nil (.snoc β A) l C)
    (hr : HasType S.Instr Ctx.nil (.snoc β B) r C)
    (hd : HasType S.Instr Ctx.nil (.snoc β C) d D) (ρ : M.Env β) :
    denote M (.let₁ (.case he hl hr) hd) ρ =
      denote M (.case he (.let₁ hl hd.underBinder) (.let₁ hr hd.underBinder))
        ρ := by
  simp only [denote_let₁, denote_case, bind_assoc, denote_underBinder]
  refine bind_congr fun x => ?_
  cases M.coprodEquiv A B x <;> rfl

/-- Soundness of the law naming the scrutinee of a pair split. -/
theorem sound_bindPair {a : Tm Empty S.Instr n} {c : Tm Empty S.Instr (n + 2)}
    {A B C : S.Ty}
    (ha : HasType S.Instr Ctx.nil β a (tensor A B))
    (hc : HasType S.Instr Ctx.nil ((β.snoc A).snoc B) c C)
    (ρ : M.Env β) :
    denote M (.let₂ ha hc) ρ =
      denote M (.let₁ ha (.let₂ HasType.newest hc.underTwoBinders)) ρ := by
  simp only [denote_let₁, denote_let₂, denote_newest, pure_bind,
    denote_underTwoBinders]

/-- Soundness of the law naming the scrutinee of a `case`. -/
theorem sound_bindCase {e : Tm Empty S.Instr n} {l r : Tm Empty S.Instr (n + 1)}
    {A B C : S.Ty}
    (he : HasType S.Instr Ctx.nil β e (coprod A B))
    (hl : HasType S.Instr Ctx.nil (.snoc β A) l C)
    (hr : HasType S.Instr Ctx.nil (.snoc β B) r C) (ρ : M.Env β) :
    denote M (.case he hl hr) ρ =
      denote M (.let₁ he (.case HasType.newest hl.underBinder hr.underBinder))
        ρ := by
  simp only [denote_let₁, denote_case, denote_newest, pure_bind,
    denote_underBinder]

/-- Soundness of the initiality law for the empty type.  The two sides may
type the bound variable differently — an `abort` types at every result type —
so this lemma is stated across two intermediate types. -/
theorem sound_emptyInitial [LawfulElgotMonad m] [InjectiveFormers S.Ty] {a : Tm Empty S.Instr n}
    {b c : Tm Empty S.Instr (n + 1)} {A A' B : S.Ty}
    (ha ha' : HasType S.Instr Ctx.nil β a empty)
    (hb : HasType S.Instr Ctx.nil (.snoc β A) b B)
    (hc : HasType S.Instr Ctx.nil (.snoc β A') c B) (ρ : M.Env β) :
    denote M (.let₁ (.abort ha) hb) ρ = denote M (.let₁ (.abort ha') hc) ρ := by
  simp only [denote_let₁, denote_abort, bind_assoc, denote_coh M ha' ha ρ]
  exact bind_congr fun z => (M.emptyEquiv z).elim

theorem sound_iterBind {n : Nat} {β : BoundCtx S.Ty n}
    {a : Tm Empty S.Instr n} {b : Tm Empty S.Instr (n + 1)} {A B : S.Ty}
    (ha : HasType S.Instr Ctx.nil β a A)
    (hb : HasType S.Instr Ctx.nil (.snoc β A) b (coprod B A))
    (ρ : M.Env β) :
    denote M (.iter ha hb) ρ =
      denote M (.let₁ ha (.iter HasType.newest hb.underBinder)) ρ := by
  simp only [denote_iter, denote_let₁, denote_newest, pure_bind,
    denote_underBinder]

theorem sound_iterFixpoint [LawfulElgotMonad m]
    {n : Nat} {β : BoundCtx S.Ty n}
    {a : Tm Empty S.Instr n} {b : Tm Empty S.Instr (n + 1)} {A B : S.Ty}
    (ha : HasType S.Instr Ctx.nil β a A)
    (hb : HasType S.Instr Ctx.nil (.snoc β A) b (coprod B A))
    (ρ : M.Env β) :
    denote M (.iter ha hb) ρ =
      denote M
        (.let₁ ha
          (.case hb HasType.newest
            (.iter HasType.newest hb.underBinder.underBinder))) ρ := by
  simp only [denote]
  apply bind_congr
  intro a
  let body := fun x : M.interp A =>
    denote M hb (ρ, x) >>= fun s =>
      pure (M.coprodEquiv B A s)
  change Elgot.iter body a = _
  rw [show Elgot.iter body a =
      (body a >>= Sum.elim pure (Elgot.iter body)) from
    congrFun (LawfulElgotMonad.fixpoint body) a]
  unfold body
  rw [bind_assoc]
  apply bind_congr
  intro s
  rw [pure_bind]
  cases hs : M.coprodEquiv B A s with
  | inl x =>
      exact (denote_newest M (β := .snoc β A)
        (ρ, a) x).symm
  | inr x =>
      have hn : denote M
          (HasType.newest (Φ := S.Instr) (Γ := Ctx.nil) (β := .snoc β A) (A := A))
            ((ρ, a), x) = pure x :=
        denote_newest M (β := .snoc β A) (ρ, a) x
      let loopBody := fun y : M.interp A =>
        denote M hb (ρ, y) >>= fun t =>
          pure (M.coprodEquiv B A t)
      calc
        Elgot.iter loopBody x = (pure x : m _) >>= Elgot.iter loopBody :=
          (pure_bind x (Elgot.iter loopBody)).symm
        _ = denote M
              (HasType.newest (Φ := S.Instr) (Γ := Ctx.nil) (β := .snoc β A) (A := A))
                ((ρ, a), x) >>= Elgot.iter loopBody :=
          congrArg (fun z => z >>= Elgot.iter loopBody) hn.symm
        _ = _ := by
          apply bind_congr
          intro _
          congr 1
          funext y
          unfold loopBody
          apply congrArg (fun z => z >>= fun t => pure (M.coprodEquiv B A t))
          calc
            denote M hb (ρ, y) =
                denote M (hb.underBinder (X := A))
                  ((ρ, a), y) :=
              (denote_underBinder M (X := A)
                hb ρ a y).symm
            _ = denote M
                ((hb.underBinder (X := A)).underBinder (X := A))
                (((ρ, a), x), y) :=
              (denote_underBinder M (X := A)
                (hb.underBinder (X := A)) (ρ, a) x y).symm

theorem sound_iterNaturality [LawfulElgotMonad m]
    {n : Nat} {β : BoundCtx S.Ty n}
    {a : Tm Empty S.Instr n} {b c : Tm Empty S.Instr (n + 1)} {A B C : S.Ty}
    (ha : HasType S.Instr Ctx.nil β a A)
    (hb : HasType S.Instr Ctx.nil (.snoc β A) b (coprod B A))
    (hc : HasType S.Instr Ctx.nil (.snoc β B) c C)
    (ρ : M.Env β) :
    denote M (.let₁ (.iter ha hb) hc) ρ =
      denote M
        (.iter ha (.case hb (.inl hc.underBinder) (.inr HasType.newest))) ρ := by
  simp only [denote, bind_assoc]
  apply bind_congr
  intro a
  let body := fun x : M.interp A =>
    denote M hb (ρ, x) >>= fun s =>
      pure (M.coprodEquiv B A s)
  let post := fun x : M.interp B => denote M hc (ρ, x)
  change Elgot.kcomp (Elgot.iter body) post a = _
  rw [show Elgot.kcomp (Elgot.iter body) post =
      Elgot.iter (Elgot.mapReturn body post) from
    LawfulElgotMonad.naturality body post]
  congr 1
  funext x
  unfold Elgot.mapReturn body post
  rw [bind_assoc]
  apply bind_congr
  intro s
  rw [pure_bind]
  cases hs : M.coprodEquiv B A s with
  | inl y =>
      simp [denote_underBinder M]
      simpa [Function.comp_def] using
        (bind_pure_comp (m := m) (fun z : M.interp C => Sum.inl z)
          (denote M hc (ρ, y)))
  | inr y =>
      simp [denote_newest M]

theorem sound_iterCodiagonal [LawfulElgotMonad m]
    {n : Nat} {β : BoundCtx S.Ty n}
    {a : Tm Empty S.Instr n} {b : Tm Empty S.Instr (n + 1)} {A B : S.Ty}
    (ha : HasType S.Instr Ctx.nil β a A)
    (hb : HasType S.Instr Ctx.nil (.snoc β A) b
      (coprod (coprod B A) A))
    (ρ : M.Env β) :
    denote M
        (.iter ha (.iter HasType.newest hb.underBinder)) ρ =
      denote M
        (.iter ha (.case hb HasType.newest (.inr HasType.newest))) ρ := by
  simp only [denote]
  apply bind_congr
  intro a
  let raw := fun x : M.interp A =>
    denote M hb (ρ, x) >>= fun s =>
      pure (M.coprodEquiv (coprod B A) A s)
  let conv := M.coprodEquiv B A
  let converted := Elgot.mapReturn raw (Elgot.liftPure conv)
  let lhs := fun x : M.interp A =>
      denote M
          (HasType.newest (Φ := S.Instr) (Γ := Ctx.nil) (β := β) (A := A)) (ρ, x) >>=
        Elgot.iter (fun y =>
          denote M (hb.underBinder (X := A))
              ((ρ, x), y) >>= fun s =>
          pure (M.coprodEquiv (coprod B A) A s)) >>= fun ba =>
        pure (M.coprodEquiv B A ba)
  have hleft : lhs = Elgot.iter converted := by
    funext x
    unfold lhs
    rw [denote_newest M, pure_bind]
    have hbody : (fun y : M.interp A =>
        denote M (hb.underBinder (X := A))
          ((ρ, x), y) >>= fun s =>
        pure (M.coprodEquiv (coprod B A) A s)) = raw := by
      funext y
      unfold raw
      apply congrArg
        (fun z => z >>= fun s =>
          pure (M.coprodEquiv (coprod B A) A s))
      exact denote_underBinder M (X := A) hb ρ x y
    rw [hbody]
    change Elgot.kcomp (Elgot.iter raw) (Elgot.liftPure conv) x = _
    exact congrFun (LawfulElgotMonad.naturality raw (Elgot.liftPure conv)) x
  change Elgot.iter lhs a = _
  rw [hleft]
  rw [show Elgot.iter (Elgot.iter converted) =
      Elgot.iter (Elgot.flattenBody converted) from
    LawfulElgotMonad.codiagonal converted]
  congr 1
  funext x
  unfold Elgot.flattenBody Elgot.kcomp Elgot.liftPure Elgot.flatten converted
  unfold Elgot.mapReturn raw conv
  simp only [Function.comp_apply, bind_assoc, pure_bind]
  apply bind_congr
  intro s
  cases hs : M.coprodEquiv (coprod B A) A s with
  | inl ba =>
      simp only [Elgot.liftPure, Function.comp_apply, pure_bind, Sum.elim_inl,
        id_eq, denote_newest]
  | inr y =>
      simp [denote_newest M]

theorem sound_iterUniformity [LawfulElgotMonad m]
    {n : Nat} {β : BoundCtx S.Ty n}
    {a : Tm Empty S.Instr n} {h b : Tm Empty S.Instr (n + 1)} {b' : Tm Empty S.Instr (n + 1)}
    {A A' B : S.Ty}
    (ha : HasType S.Instr Ctx.nil β a A)
    (hh : HasType S.Instr Ctx.nil (.snoc β A) h A') (hp : Pure S.pureEff h)
    (hb : HasType S.Instr Ctx.nil (.snoc β A) b (coprod B A))
    (hb' : HasType S.Instr Ctx.nil (.snoc β A') b' (coprod B A'))
    (hsquare : ∀ (ρA : M.Env (.snoc β A)),
      denote M
          (.case hb (.inl HasType.newest) (.inr hh.underBinder)) ρA =
        denote M ((hb'.underBinder).instantiate hh) ρA)
    (ρ : M.Env β) :
    denote M (.iter ha hb) ρ =
      denote M (.iter (.let₁ ha hh) hb') ρ := by
  classical
  let hfun := fun x : M.interp A => Classical.choose
    (denote_pure_factor M hp hh (ρ, x))
  have hhfun (x : M.interp A) :
      denote M hh (ρ, x) = pure (hfun x) :=
    Classical.choose_spec (denote_pure_factor M hp hh (ρ, x))
  let f := fun x : M.interp A =>
    denote M hb (ρ, x) >>= fun s =>
      pure (M.coprodEquiv B A s)
  let g := fun x : M.interp A' =>
    denote M hb' (ρ, x) >>= fun s =>
      pure (M.coprodEquiv B A' s)
  have comm : Elgot.kcomp f (Elgot.liftPure (Sum.map id hfun)) =
      Elgot.kcomp (Elgot.liftPure hfun) g := by
    funext x
    have sq := hsquare (ρ, x)
    rw [denote_instantiate M 
      (hb'.underBinder (X := A)) hh (ρ, x) (hfun x) (hhfun x)] at sq
    rw [denote_underBinder M (X := A)
      hb' ρ x (hfun x)] at sq
    calc
      Elgot.kcomp f (Elgot.liftPure (Sum.map id hfun)) x =
          denote M
              (.case hb (.inl HasType.newest) (.inr hh.underBinder)) (ρ, x) >>=
            fun s => pure (M.coprodEquiv B A' s) := by
        unfold f Elgot.kcomp Elgot.liftPure
        simp only [Function.comp_apply, denote, bind_assoc,
          pure_bind]
        apply bind_congr
        intro s
        cases hs : M.coprodEquiv B A s with
        | inl y => simp [denote_newest M]
        | inr y => simp [denote_underBinder M, hhfun]
      _ = denote M hb'  (ρ, hfun x) >>=
            fun s => pure (M.coprodEquiv B A' s) :=
        congrArg (fun z => z >>= fun s => pure (M.coprodEquiv B A' s)) sq
      _ = Elgot.kcomp (Elgot.liftPure hfun) g x := by
        unfold g Elgot.kcomp Elgot.liftPure
        simp only [Function.comp_apply, pure_bind]
  have hu := LawfulElgotMonad.uniformity f g hfun comm
  simp only [denote, bind_assoc]
  apply bind_congr
  intro x
  change Elgot.iter f x = _
  rw [hu]
  unfold Elgot.kcomp Elgot.liftPure
  simp only [Function.comp_apply, pure_bind]
  rw [hhfun x, pure_bind]


end Axioms

end Isotope.LambdaIter.Monadic
