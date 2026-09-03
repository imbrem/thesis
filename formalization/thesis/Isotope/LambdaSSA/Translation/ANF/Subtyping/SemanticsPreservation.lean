import Isotope.LambdaSSA.Translation.ANF.Subtyping.Semantics
import Isotope.LambdaIter.Subtyping.Semantics.Substitution

/-! # Semantic preservation for proof-relevant ANF elaboration -/

namespace Isotope.LambdaSSA.Translation.ANF.Subtyping

set_option relaxedAutoImplicit true

open Isotope.Elgot Isotope.LambdaIter
open Isotope.LambdaIter.LocallyNameless
open Isotope.LambdaIter.Subtyping.Semantics
open Isotope.LambdaSSA.Translation.ANF.Elaboration

universe u v w q r

variable {τ : Type u} [TypeFormers τ] [LambdaIter.Subtyping τ] [TypeModel.{u, v} τ]
variable {ν : Type w} [DecidableEq ν] {Φ : Type q} [HasTy Φ τ]
variable {ε : Type r} [HasEff Φ ε] [Bot ε]
variable {m : Type v → Type v} [Monad m] [LawfulMonad m]
variable [Iterate m] [LawfulElgotMonad m] [InstructionModel Φ τ ε m]

private def toSubRenaming {β : BoundCtx τ n} {β' : BoundCtx τ k}
    (r : TypedRenaming β β') :
    LambdaIter.Subtyping.LocallyNameless.TypedRenaming β β' where
  toFun := r.toFun
  typed := r.typed

private theorem denoteAtom_bv_transport {Γ : Ctx ν τ} {β : BoundCtx τ n}
    (i : Fin n) {A : τ} (e : β.get i = A)
    (γ : CtxDen Γ) (ρ : BoundDen β) :
    denoteAtom (m := m) (ε := ε)
        (e ▸ (Atom.HasType.bv (Φ := Φ) (Γ := Γ) (β := β) (i := i))) γ ρ =
      (pure (e ▸ BoundDen.get ρ i) : m (TyDen A)) := by
  cases e
  rfl

private theorem pull_toSub_underBinder {β : BoundCtx τ n} {X A : τ}
    (ρ : BoundDen β) (x : TyDen X) (a : TyDen A) :
    BoundDen.pull (toSubRenaming (TypedRenaming.underBinder β X A))
      ((ρ, x), a) = (ρ, a) := by
  apply Prod.ext
  · exact BoundDen.pull_succ β X ρ x
  · rfl

private def insertTwo {β : BoundCtx τ n} (X Y A : τ) :
    TypedRenaming (.snoc β A) (.snoc (.snoc (.snoc β X) Y) A) where
  toFun := fun i => Fin.cases 0 (fun i => Fin.succ (Fin.succ (Fin.succ i))) i
  typed := Fin.cases rfl (fun _ => rfl)

private theorem pull_toSub_insertTwo {β : BoundCtx τ n} {X Y A : τ}
    (ρ : BoundDen β) (x : TyDen X) (y : TyDen Y) (a : TyDen A) :
    BoundDen.pull (toSubRenaming (insertTwo (β := β) X Y A))
      (((ρ, x), y), a) = (ρ, a) := by
  apply Prod.ext
  · exact BoundDen.pull_succ β X ρ x
  · rfl

private def succForTyping {Γ : Ctx ν τ} {β : BoundCtx τ n}
    {t : LambdaIter.LocallyNameless.Tm ν Φ n} {A : τ}
    (_ : LambdaIter.Subtyping.LocallyNameless.HasType Φ Γ β t A) :
    TypedRenaming β (.snoc β A) := TypedRenaming.succ β A

private def underTwoForTyping {Γ : Ctx ν τ} {β : BoundCtx τ n}
    {a : LambdaIter.LocallyNameless.Tm ν Φ n} {A B : τ}
    (_ : LambdaIter.Subtyping.LocallyNameless.HasType Φ Γ β a (tensor A B))
    {b : LambdaIter.LocallyNameless.Tm ν Φ (n + 2)} {C : τ}
    (_ : LambdaIter.Subtyping.LocallyNameless.HasType Φ Γ
      (.snoc (.snoc β A) B) b C) :
    TypedRenaming (.snoc (.snoc β A) B)
      (.snoc (.snoc (.snoc β (tensor A B)) A) B) :=
  TypedRenaming.underTwoBinders β (tensor A B) A B

private def underForTyping {Γ : Ctx ν τ} {β : BoundCtx τ n}
    {a : LambdaIter.LocallyNameless.Tm ν Φ n} {X : τ}
    (_ : LambdaIter.Subtyping.LocallyNameless.HasType Φ Γ β a X)
    {b : LambdaIter.LocallyNameless.Tm ν Φ (n + 1)} {A C : τ}
    (_ : LambdaIter.Subtyping.LocallyNameless.HasType Φ Γ (.snoc β A) b C) :
    TypedRenaming (.snoc β A) (.snoc (.snoc β X) A) :=
  TypedRenaming.underBinder β X A

private def caseDen {Γ : Ctx ν τ} {β : BoundCtx τ n}
    {e : LambdaIter.LocallyNameless.Tm ν Φ n} {X Y C : τ}
    (_ : LambdaIter.Subtyping.LocallyNameless.HasType Φ Γ β e (coprod X Y))
    {l r : LambdaIter.LocallyNameless.Tm ν Φ (n + 1)}
    (hl : LambdaIter.Subtyping.LocallyNameless.HasType Φ Γ (.snoc β X) l C)
    (hr : LambdaIter.Subtyping.LocallyNameless.HasType Φ Γ (.snoc β Y) r C)
    (γ : CtxDen Γ) (ρ : BoundDen β) : TyDen (coprod X Y) → m (TyDen C) :=
  fun e' => match TypeModel.coprodEquiv X Y e' with
    | .inl a => LambdaIter.Subtyping.Semantics.denote (m := m) (ε := ε) hl γ (ρ, a)
    | .inr b => LambdaIter.Subtyping.Semantics.denote (m := m) (ε := ε) hr γ (ρ, b)

private def iterDen {Γ : Ctx ν τ} {β : BoundCtx τ n}
    {a : LambdaIter.LocallyNameless.Tm ν Φ n} {A B : τ}
    (_ : LambdaIter.Subtyping.LocallyNameless.HasType Φ Γ β a A)
    {b : LambdaIter.LocallyNameless.Tm ν Φ (n + 1)}
    (hb : LambdaIter.Subtyping.LocallyNameless.HasType Φ Γ (.snoc β A) b (coprod B A))
    (γ : CtxDen Γ) (ρ : BoundDen β) : TyDen A → m (TyDen B ⊕ TyDen A) :=
  fun a => LambdaIter.Subtyping.Semantics.denote (m := m) (ε := ε) hb γ (ρ, a) >>= fun s =>
    (pure (TypeModel.coprodEquiv B A s) : m (TyDen B ⊕ TyDen A))

private def iterElabDen {Γ : Ctx ν τ} {β : BoundCtx τ n}
    {a : LambdaIter.LocallyNameless.Tm ν Φ n} {A B : τ}
    (ha : LambdaIter.Subtyping.LocallyNameless.HasType Φ Γ β a A)
    {b : LambdaIter.LocallyNameless.Tm ν Φ (n + 1)}
    (hb : LambdaIter.Subtyping.LocallyNameless.HasType Φ Γ (.snoc β A) b (coprod B A))
    (γ : CtxDen Γ) (ρ : BoundDen β) (ambient : TyDen A) :
    TyDen A → m (TyDen B ⊕ TyDen A) :=
  fun x => denoteProgram (m := m) (ε := ε)
    (programRename_hasType (underForTyping ha hb) (elaborate_hasType hb)) γ
      ((ρ, ambient), x) >>= fun s =>
        (pure (TypeModel.coprodEquiv B A s) : m (TyDen B ⊕ TyDen A))

@[simp] private theorem get_zero {β : BoundCtx τ n} {A : τ}
    (ρ : BoundDen β) (a : TyDen A) :
    BoundDen.get (β := .snoc β A) (ρ, a) 0 = a := rfl

@[simp] private theorem get_one {β : BoundCtx τ n} {A B : τ}
    (ρ : BoundDen β) (a : TyDen A) (b : TyDen B) :
    BoundDen.get (β := .snoc (.snoc β A) B) ((ρ, a), b) 1 = a := rfl

mutual
  /-- Direct semantic naturality of proof-relevant ANF programs. -/
  theorem denoteProgram_rename {Γ : Ctx ν τ} {β : BoundCtx τ n}
      {β' : BoundCtx τ k} {p : ANF.Program ν Φ n} {A : τ}
      (h : Program.HasType Γ β p A) (r : TypedRenaming β β')
      (γ : CtxDen Γ) (ρ : BoundDen β') :
      denoteProgram (m := m) (ε := ε) (programRename_hasType r h) γ ρ =
        denoteProgram (m := m) (ε := ε) h γ
          (BoundDen.pull (toSubRenaming r) ρ) := by
    cases h with
    | ret ha => exact denoteAtom_rename ha r γ ρ
    | let₁ hi hb =>
        simp only [programRename_hasType, denoteProgram]
        rw [denoteInstr_rename hi r γ ρ]
        apply bind_congr
        intro a
        simpa only [toSubRenaming, BoundDen.pull_up] using
          denoteProgram_rename hb (r.up _) γ (ρ, a)
    | let₂ ha hb =>
        simp only [programRename_hasType, denoteProgram]
        rw [denoteAtom_rename ha r γ ρ]
        apply bind_congr
        intro ab
        simpa only [toSubRenaming, BoundDen.pull_up] using
          denoteProgram_rename hb ((r.up _).up _) γ
            ((ρ, (TypeModel.tensorEquiv _ _ ab).1),
              (TypeModel.tensorEquiv _ _ ab).2)

  /-- Direct semantic naturality of proof-relevant ANF instructions. -/
  theorem denoteInstr_rename {Γ : Ctx ν τ} {β : BoundCtx τ n}
      {β' : BoundCtx τ k} {i : ANF.Instr ν Φ n} {A : τ}
      (h : Instr.HasType Γ β i A) (r : TypedRenaming β β')
      (γ : CtxDen Γ) (ρ : BoundDen β') :
      denoteInstr (m := m) (ε := ε) (instrRename_hasType r h) γ ρ =
        denoteInstr (m := m) (ε := ε) h γ
          (BoundDen.pull (toSubRenaming r) ρ) := by
    cases h with
    | atom ha => exact denoteAtom_rename ha r γ ρ
    | case he hl hr =>
        simp only [instrRename_hasType, denoteInstr]
        rw [denoteAtom_rename he r γ ρ]
        apply bind_congr
        intro e
        cases TypeModel.coprodEquiv _ _ e with
        | inl a =>
            simp only
            simpa only [toSubRenaming, BoundDen.pull_up] using
              denoteProgram_rename hl (r.up _) γ (ρ, a)
        | inr b =>
            simp only
            simpa only [toSubRenaming, BoundDen.pull_up] using
              denoteProgram_rename hr (r.up _) γ (ρ, b)
    | iter ha hb =>
        simp only [instrRename_hasType, denoteInstr]
        rw [denoteAtom_rename ha r γ ρ]
        apply bind_congr
        intro a
        congr 1
        funext x
        simpa only [toSubRenaming, BoundDen.pull_up] using congrArg
          (fun z => z >>= fun s => pure (TypeModel.coprodEquiv _ _ s))
          (denoteProgram_rename hb (r.up _) γ (ρ, x))

  /-- Direct semantic naturality of proof-relevant ANF atoms.  In particular,
  the subtype witness in `.sub` is retained on both sides. -/
  theorem denoteAtom_rename {Γ : Ctx ν τ} {β : BoundCtx τ n}
      {β' : BoundCtx τ k} {a : ANF.Atom ν Φ n} {A : τ}
      (h : Atom.HasType Γ β a A) (r : TypedRenaming β β')
      (γ : CtxDen Γ) (ρ : BoundDen β') :
      denoteAtom (m := m) (ε := ε) (atomRename_hasType r h) γ ρ =
        denoteAtom (m := m) (ε := ε) h γ
          (BoundDen.pull (toSubRenaming r) ρ) := by
    induction h with
    | fv hx => rfl
    | bv =>
        simp only [atomRename_hasType, denoteAtom]
        calc
          _ = pure (r.typed _ ▸ BoundDen.get ρ (r.toFun _)) :=
            denoteAtom_bv_transport (i := r.toFun _) (e := r.typed _) γ ρ
          _ = _ := congrArg pure (BoundDen.get_pull (toSubRenaming r) ρ _).symm
    | op h ih => simp only [atomRename_hasType, denoteAtom]; rw [ih]
    | unit => rfl
    | pair ha hb iha ihb =>
        simp only [atomRename_hasType, denoteAtom]
        rw [iha, ihb]
    | inl h ih | inr h ih | abort h ih | sub h _ ih =>
        simp only [atomRename_hasType, denoteAtom]
        rw [ih]
end

/-- ANF `bind` denotes Kleisli sequencing.  The proof follows the first
program structurally, retaining all proof-relevant atom derivations. -/
theorem denoteProgram_bind {Γ : Ctx ν τ} {β : BoundCtx τ n}
    {p : ANF.Program ν Φ n} {A B : τ} {k : ANF.Program ν Φ (n + 1)}
    (hp : Program.HasType Γ β p A)
    (hk : Program.HasType Γ (.snoc β A) k B)
    (γ : CtxDen Γ) (ρ : BoundDen β) :
    denoteProgram (m := m) (ε := ε) (bind_hasType hp hk) γ ρ =
      (denoteProgram (m := m) (ε := ε) hp γ ρ >>= fun a =>
        denoteProgram (m := m) (ε := ε) hk γ (ρ, a)) := by
  fun_induction bind_hasType hp hk
  next ha hk => rfl
  next n β A k X i hi body hb hk ih =>
      simp only [denoteProgram]
      rw [LawfulMonad.bind_assoc]
      apply bind_congr
      intro x
      calc
        _ = denoteProgram hb γ (ρ, x) >>= fun a =>
              denoteProgram (programRename_hasType
                (TypedRenaming.underBinder β X A) hk) γ ((ρ, x), a) := ih (ρ, x)
        _ = _ := by
          apply bind_congr
          intro a
          rw [denoteProgram_rename (m := m) (ε := ε) hk
            (TypedRenaming.underBinder β X A) γ ((ρ, x), a)]
          rw [pull_toSub_underBinder]
  next n β A k X Y atom ha body hb hk ih =>
      simp only [denoteProgram]
      rw [LawfulMonad.bind_assoc]
      apply bind_congr
      intro ab
      let xy := TypeModel.tensorEquiv _ _ ab
      let ri := insertTwo (β := β) X Y A
      calc
        _ = denoteProgram hb γ ((ρ, xy.1), xy.2) >>= fun a =>
              denoteProgram (programRename_hasType ri hk) γ (((ρ, xy.1), xy.2), a) :=
            ih ((ρ, xy.1), xy.2)
        _ = _ := by
          apply bind_congr
          intro a
          rw [denoteProgram_rename (m := m) (ε := ε) hk ri γ
            (((ρ, xy.1), xy.2), a)]
          rw [pull_toSub_insertTwo]

/-- Pushing a coercion to the returned atom has exactly the denotation of
postcomposing with the selected subtype witness. -/
theorem denoteProgram_coerceResult {Γ : Ctx ν τ} {β : BoundCtx τ n}
    {p : ANF.Program ν Φ n} {A B : τ}
    (hp : Program.HasType Γ β p A) (d : Subty A B)
    (γ : CtxDen Γ) (ρ : BoundDen β) :
    denoteProgram (m := m) (ε := ε) (hp.coerceResult d) γ ρ =
      (denoteProgram (m := m) (ε := ε) hp γ ρ >>= fun a =>
        pure (coeSub d a)) := by
  fun_induction Program.HasType.coerceResult d hp
  next ha => rfl
  next hi hb ih =>
      simp only [Program.HasType.coerceResult, denoteProgram, ih]
      exact (LawfulMonad.bind_assoc _ _ _).symm
  next ha hb ih =>
      simp only [Program.HasType.coerceResult, denoteProgram]
      rw [LawfulMonad.bind_assoc]
      apply bind_congr
      intro ab
      exact ih _

/-- Proof-relevant administrative elaboration preserves the direct monadic
denotation of every lambda-iter typing derivation. -/
theorem denote_elaborate {Γ : Ctx ν τ} {β : BoundCtx τ n}
    {t : LambdaIter.LocallyNameless.Tm ν Φ n} {A : τ}
    (h : LambdaIter.Subtyping.LocallyNameless.HasType Φ Γ β t A)
    (γ : CtxDen Γ) (ρ : BoundDen β) :
    denoteProgram (m := m) (ε := ε) (elaborate_hasType h) γ ρ =
      LambdaIter.Subtyping.Semantics.denote (m := m) (ε := ε) h γ ρ := by
  induction h with
  | fv hx =>
      unfold elaborate_hasType denoteProgram denoteAtom
        LambdaIter.Subtyping.Semantics.denote
      rfl
  | bv =>
      unfold elaborate_hasType denoteProgram denoteAtom
        LambdaIter.Subtyping.Semantics.denote
      rfl
  | op h ih =>
      simp only [elaborate_hasType, elaborate]
      unfold LambdaIter.Subtyping.Semantics.denote
      conv_lhs => rw [denoteProgram_bind]
      simp only [ih, denoteProgram, denoteInstr, denoteAtom,
        LambdaIter.Subtyping.Semantics.denote]
      unfold BoundDen.get
      simp only [Fin.cases_zero]
      apply bind_congr
      intro a
      exact LawfulMonad.pure_bind _ _
  | let₁ ha hb iha ihb =>
      simp only [elaborate_hasType, elaborate]
      unfold LambdaIter.Subtyping.Semantics.denote
      conv_lhs => rw [denoteProgram_bind]
      simp only [iha, ihb, LambdaIter.Subtyping.Semantics.denote]
  | unit =>
      unfold elaborate_hasType denoteProgram denoteAtom
        LambdaIter.Subtyping.Semantics.denote
      rfl
  | pair ha hb iha ihb =>
      simp only [elaborate_hasType, elaborate]
      unfold LambdaIter.Subtyping.Semantics.denote
      conv_lhs => rw [denoteProgram_bind]
      simp only [iha]
      apply bind_congr
      intro a
      conv_lhs => rw [denoteProgram_bind]
      simp only [denoteProgram, denoteAtom, get_zero, get_one, pure_bind, bind_pure]
      have hr := denoteProgram_rename (m := m) (ε := ε) (elaborate_hasType hb)
        (succForTyping ha) γ (ρ, a)
      change (denoteProgram
        (programRename_hasType (succForTyping ha) (elaborate_hasType hb)) γ (ρ, a)
          >>= _) = _
      rw [hr]
      have ep : BoundDen.pull (toSubRenaming (succForTyping ha)) (ρ, a) = ρ := by
        simpa only [succForTyping, toSubRenaming] using
          BoundDen.pull_succ _ _ ρ a
      rw [ep, ihb]
      apply bind_congr
      intro b
      unfold BoundDen.get
      simp only [Fin.cases_zero]
      exact (LawfulMonad.pure_bind _ _).trans (LawfulMonad.pure_bind _ _)
  | let₂ ha hb iha ihb =>
      simp only [elaborate_hasType, elaborate]
      unfold LambdaIter.Subtyping.Semantics.denote
      conv_lhs => rw [denoteProgram_bind]
      simp only [iha]
      apply bind_congr
      intro ab
      simp only [denoteProgram, denoteAtom, get_zero, pure_bind, bind_pure]
      have hr := denoteProgram_rename (m := m) (ε := ε) (elaborate_hasType hb)
        (underTwoForTyping ha hb) γ
        (((ρ, ab), (TypeModel.tensorEquiv _ _ ab).1),
          (TypeModel.tensorEquiv _ _ ab).2)
      have ep : BoundDen.pull (toSubRenaming (underTwoForTyping ha hb))
          (((ρ, ab), (TypeModel.tensorEquiv _ _ ab).1),
            (TypeModel.tensorEquiv _ _ ab).2) =
          ((ρ, (TypeModel.tensorEquiv _ _ ab).1),
            (TypeModel.tensorEquiv _ _ ab).2) := by
        simpa only [underTwoForTyping, toSubRenaming] using
          BoundDen.pull_underTwoBinders _ _ _ _ ρ ab
            (TypeModel.tensorEquiv _ _ ab).1 (TypeModel.tensorEquiv _ _ ab).2
      calc
        _ = denoteProgram
            (programRename_hasType (underTwoForTyping ha hb) (elaborate_hasType hb)) γ
              (((ρ, ab), (TypeModel.tensorEquiv _ _ ab).1),
                (TypeModel.tensorEquiv _ _ ab).2) := LawfulMonad.pure_bind _ _
        _ = _ := hr
        _ = _ := by rw [ep, ihb]; rfl
  | inl h ih =>
      simp only [elaborate_hasType, elaborate]
      unfold LambdaIter.Subtyping.Semantics.denote
      conv_lhs => rw [denoteProgram_bind]
      simp only [ih, denoteProgram, denoteInstr, denoteAtom,
        LambdaIter.Subtyping.Semantics.denote]
      unfold BoundDen.get
      simp only [Fin.cases_zero]
      apply bind_congr
      intro a
      exact LawfulMonad.pure_bind _ _
  | inr h ih =>
      simp only [elaborate_hasType, elaborate]
      unfold LambdaIter.Subtyping.Semantics.denote
      conv_lhs => rw [denoteProgram_bind]
      simp only [ih, denoteProgram, denoteInstr, denoteAtom,
        LambdaIter.Subtyping.Semantics.denote]
      unfold BoundDen.get
      simp only [Fin.cases_zero]
      apply bind_congr
      intro b
      exact LawfulMonad.pure_bind _ _
  | case he hl hr ihe ihl ihr =>
      simp only [elaborate_hasType, elaborate]
      unfold LambdaIter.Subtyping.Semantics.denote
      conv_lhs => rw [denoteProgram_bind]
      simp only [ihe]
      apply bind_congr
      intro e
      simp only [denoteProgram, denoteInstr, denoteAtom, get_zero, pure_bind, bind_pure]
      cases heq : TypeModel.coprodEquiv _ _ e with
      | inl a =>
          simp_rw [denoteProgram_rename]
          simp only [pull_toSub_underBinder, ihl, ihr,
            LambdaIter.Subtyping.Semantics.denote]
          unfold BoundDen.get
          simp only [Fin.cases_zero]
          let F := caseDen (m := m) (ε := ε) he hl hr γ ρ
          change ((pure e >>= F) >>= pure) = _
          rw [bind_pure, LawfulMonad.pure_bind]
          dsimp [F]
          unfold caseDen
          rw [heq]
      | inr b =>
          simp_rw [denoteProgram_rename]
          simp only [pull_toSub_underBinder, ihl, ihr,
            LambdaIter.Subtyping.Semantics.denote]
          unfold BoundDen.get
          simp only [Fin.cases_zero]
          let F := caseDen (m := m) (ε := ε) he hl hr γ ρ
          change ((pure e >>= F) >>= pure) = _
          rw [bind_pure, LawfulMonad.pure_bind]
          dsimp [F]
          unfold caseDen
          rw [heq]
  | abort h ih =>
      simp only [elaborate_hasType, elaborate]
      unfold LambdaIter.Subtyping.Semantics.denote
      conv_lhs => rw [denoteProgram_bind]
      simp only [ih, denoteProgram, denoteInstr, denoteAtom,
        LambdaIter.Subtyping.Semantics.denote]
      unfold BoundDen.get
      simp only [Fin.cases_zero]
      apply bind_congr
      intro z
      exact LawfulMonad.pure_bind _ _
  | iter ha hb iha ihb =>
      simp only [elaborate_hasType, elaborate]
      unfold LambdaIter.Subtyping.Semantics.denote
      conv_lhs => rw [denoteProgram_bind]
      simp only [iha]
      apply bind_congr
      intro a
      simp only [denoteProgram, denoteInstr, denoteAtom, get_zero, pure_bind, bind_pure]
      unfold BoundDen.get
      simp only [Fin.cases_zero]
      let G := iterDen (m := m) (ε := ε) ha hb γ ρ
      refine (bind_pure _).trans ?_
      apply congrArg (fun f => iter f a)
      funext x
      dsimp [G, iterDen]
      have hr := denoteProgram_rename (m := m) (ε := ε) (elaborate_hasType hb)
        (underForTyping ha hb) γ ((ρ, a), x)
      have ep : BoundDen.pull (toSubRenaming (underForTyping ha hb))
          ((ρ, a), x) = (ρ, x) := by
        simpa only [underForTyping, toSubRenaming] using
          BoundDen.pull_underBinder _ _ _ ρ a x
      change (denoteProgram
        (programRename_hasType (underForTyping ha hb) (elaborate_hasType hb)) γ
          ((ρ, a), x) >>= fun s => pure (TypeModel.coprodEquiv _ _ s)) = _
      rw [hr, ep, ihb]
      rfl
  | sub h d ih =>
      simp only [elaborate_hasType]
      unfold LambdaIter.Subtyping.Semantics.denote
      rw [denoteProgram_coerceResult (m := m) (ε := ε) _ d γ ρ, ih]

end Isotope.LambdaSSA.Translation.ANF.Subtyping
