import Isotope.LambdaSSA.Translation.ANF.ToSSA.Subtyping
import Isotope.LambdaSSA.Translation.ANF.Subtyping.Semantics
import Isotope.LambdaSSA.Subtyping.Semantics.Monadic.Region

/-! # Monadic correctness of proof-relevant ANF-to-SSA compilation -/

namespace Isotope.LambdaSSA.Translation.ANF.ToSSA.Subtyping

set_option relaxedAutoImplicit true

open Isotope.LambdaIter
open Isotope.LambdaIter.Subtyping.Semantics
open Isotope.LambdaSSA.Translation.ANF
open Isotope.LambdaSSA.Semantics.Monadic

universe u v q r

variable {τ : Type u} [TypeFormers τ] [LambdaIter.Subtyping τ] [TypeModel.{u, v} τ]
variable {Φ : Type q} [HasTy Φ τ] {ε : Type r} [HasEff Φ ε] [Bot ε]
variable {m : Type v → Type v} [Monad m] [LawfulMonad m]
variable [Isotope.Elgot.Iterate m] [Isotope.Elgot.LawfulElgotMonad m]
variable [InstructionModel Φ τ ε m]

def envToBound : {β : LambdaIter.LocallyNameless.BoundCtx τ n} →
    Env (LambdaSSA.LocallyNameless.ToDeBruijn.context β) → BoundDen β
  | .nil, _ => PUnit.unit
  | .snoc _ _, ρ => (envToBound ρ.1, ρ.2)

@[simp] theorem envToBound_snoc
    {β : LambdaIter.LocallyNameless.BoundCtx τ n} {A : τ}
    (ρ : Env (LambdaSSA.LocallyNameless.ToDeBruijn.context β)) (a : TyDen A) :
    envToBound (β := β.snoc A) (ρ, a) = (envToBound ρ, a) := rfl

@[simp] theorem env_get_context
    {β : LambdaIter.LocallyNameless.BoundCtx τ n}
    (ρ : Env (LambdaSSA.LocallyNameless.ToDeBruijn.context β)) (i : Fin n) :
    Env.get ρ i.val (LambdaSSA.LocallyNameless.ToDeBruijn.getElem_context β i) =
      BoundDen.get (envToBound ρ) i := by
  induction β with
  | nil => exact Fin.elim0 i
  | snoc β A ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · simpa [Env.get, BoundDen.get] using ih ρ.1 j

/-- Atom compilation retains every explicit subtype witness. -/
theorem atom_denotes {β : LambdaIter.LocallyNameless.BoundCtx τ n}
    {a : ANF.Atom Empty Φ n} {A : τ}
    (h : ANF.Subtyping.Atom.HasType (Ctx.nil : Ctx Empty τ) β a A) :
    Isotope.LambdaSSA.Subtyping.Semantics.Monadic.Denotes ε (atom_hasType h)
      (fun ρ => ANF.Subtyping.denoteAtom (m := m) (ε := ε) h PUnit.unit
        (envToBound ρ)) := by
  induction h with
  | fv h => cases h
  | bv => simpa [ANF.Subtyping.denoteAtom, envToBound, env_get_context] using
      (Isotope.LambdaSSA.Subtyping.Semantics.Monadic.Denotes.var
        (Φ := Φ) (ε := ε) (m := m)
        (LambdaSSA.LocallyNameless.ToDeBruijn.getElem_context _ _))
  | op _ ih => exact .op ih
  | unit => exact .unit
  | pair _ _ iha ihb => exact .pair iha ihb
  | inl _ ih => exact .inl ih
  | inr _ ih => exact .inr ih
  | abort _ ih => exact .abort ih
  | sub _ d ih => exact .sub ih d

noncomputable def resultEval {β : LambdaIter.LocallyNameless.BoundCtx τ n}
    {p : ANF.Program Empty Φ n} {A C : τ}
    (h : ANF.Subtyping.Program.HasType (Ctx.nil : Ctx Empty τ) β p A)
    (hAC : Subty A C) {L : LambdaSSA.LCtx τ} {result : Nat}
    (hout : LambdaSSA.At L result C) :
    Env (LambdaSSA.LocallyNameless.ToDeBruijn.context β) → m (LabelDen L) :=
  fun ρ => ANF.Subtyping.denoteProgram (m := m) (ε := ε) h PUnit.unit
    (envToBound ρ) >>= fun a => pure (coeSub hAC a) >>= fun c =>
      pure (labelInject result hout c)

theorem ret_denotes {β : LambdaIter.LocallyNameless.BoundCtx τ n}
    {a : ANF.Atom Empty Φ n} {A C : τ}
    (ha : ANF.Subtyping.Atom.HasType (Ctx.nil : Ctx Empty τ) β a A)
    (hAC : Subty A C) {L : LambdaSSA.LCtx τ} {result : Nat}
    (hout : LambdaSSA.At L result C) :
    Isotope.LambdaSSA.Subtyping.Semantics.Monadic.RegionDenotes ε
      (simpleProgram_hasType (.ret a) (.ret ha) hAC hout)
      (resultEval (ε := ε) (m := m) (.ret ha) hAC hout) := by
  rw [simpleProgram_hasType]
  unfold resultEval ANF.Subtyping.denoteProgram
  simpa only [LawfulMonad.bind_assoc] using
    (Isotope.LambdaSSA.Subtyping.Semantics.Monadic.RegionDenotes.br
    (ε := ε) (m := m) (h := hout)
    (Isotope.LambdaSSA.Subtyping.Semantics.Monadic.Denotes.sub
      (atom_denotes (ε := ε) (m := m) ha) hAC))

theorem let₁_atom_denotes {β : LambdaIter.LocallyNameless.BoundCtx τ n}
    {a : ANF.Atom Empty Φ n} {body : ANF.Program Empty Φ (n + 1)}
    {X A C : τ}
    (ha : ANF.Subtyping.Atom.HasType (Ctx.nil : Ctx Empty τ) β a X)
    (hb : ANF.Subtyping.Program.HasType (Ctx.nil : Ctx Empty τ)
      (β.snoc X) body A) (hAC : Subty A C) (hs : ToSSA.SimpleProgram body)
    {L : LambdaSSA.LCtx τ} {result : Nat} (hout : LambdaSSA.At L result C)
    (db : Isotope.LambdaSSA.Subtyping.Semantics.Monadic.RegionDenotes ε
      (simpleProgram_hasType hs hb hAC hout)
      (resultEval (ε := ε) (m := m) hb hAC hout)) :
    Isotope.LambdaSSA.Subtyping.Semantics.Monadic.RegionDenotes ε
      (simpleProgram_hasType (.let₁ (.atom a) hs) (.let₁ (.atom ha) hb) hAC hout)
      (resultEval (ε := ε) (m := m) (.let₁ (.atom ha) hb) hAC hout) := by
  rw [simpleProgram_hasType]
  unfold resultEval at db ⊢
  simpa only [ANF.Subtyping.denoteProgram, ANF.Subtyping.denoteInstr,
    LawfulMonad.bind_assoc] using
    (Isotope.LambdaSSA.Subtyping.Semantics.Monadic.RegionDenotes.let₁
      (atom_denotes (ε := ε) (m := m) ha) db)

/-- A one-block CFG whose entry always transfers to its block and whose block
always transfers to an external continuation contracts to their sequential
composition. -/
theorem cfgOne_denotes
    {Γ : LambdaSSA.VCtx τ} {L : LambdaSSA.LCtx τ} {X A : τ}
    {entry block : LambdaSSA.Region Φ}
    (he : LambdaSSA.Subtyping.Region.HasType Γ entry (X :: L))
    (hb : LambdaSSA.Subtyping.Region.HasType (X :: Γ) block (X :: L))
    {f : Env Γ → m (TyDen X)}
    {g : Env (X :: Γ) → m (TyDen A)}
    {result : Nat} (hout : LambdaSSA.At L result A)
    (de : Isotope.LambdaSSA.Subtyping.Semantics.Monadic.RegionDenotes ε he (fun ρ => f ρ >>= fun x =>
      pure (labelInject 0 (by simp [LambdaSSA.At]) x)))
    (db : Isotope.LambdaSSA.Subtyping.Semantics.Monadic.RegionDenotes ε hb (fun ρ => g ρ >>= fun a =>
      pure (labelInject (result + 1) (at_succ hout) a))) :
    Isotope.LambdaSSA.Subtyping.Semantics.Monadic.RegionDenotes ε
      (LambdaSSA.Subtyping.Region.HasType.cfg (fun _ : Fin 1 => X) he (fun _ => hb))
      (fun ρ => f ρ >>= fun x => g (ρ, x) >>= fun a =>
        pure (labelInject result hout a)) := by
  let collective : Env Γ × FiniteLabelDen (fun _ : Fin 1 => X) →
      m (LabelDen ([X] ++ L)) :=
    fun p => g (p.1, p.2.2) >>= fun a =>
      pure (labelInject (result + 1) (at_succ hout) a)
  have dc : CollectiveDenotes Γ (fun _ : Fin 1 => X) L
      (fun _ => fun ρ => g ρ >>= fun a =>
        pure (labelInject (result + 1) (at_succ hout) a)) collective := by
    constructor
    intro i ρ x
    rfl
  have dcfg := Isotope.LambdaSSA.Subtyping.Semantics.Monadic.RegionDenotes.cfg (R := fun _ : Fin 1 => X)
    (collective := collective) he (fun _ => hb) de (fun _ => db) dc
  convert dcfg using 1
  funext ρ
  simp only [binaryCoproductIso_hom_labelAppendSplit]
  change _ = (f ρ >>= fun x => pure (labelInject 0 (by
    simp [LambdaSSA.At]) x)) >>= fun target => _
  conv_rhs => rw [LawfulMonad.bind_assoc]
  apply bind_congr
  intro x
  simp only [LawfulMonad.pure_bind, labelInject_eq_recursive]
  generalize_proofs hentry
  have hr := LabelValue.appendSplit_ofFn_one_inject_zero L X hentry x
  split <;> rename_i hm
  · have hc := hr.symm.trans hm
    contradiction
  · have hc := Sum.inr.inj (hr.symm.trans hm)
    cases hc
    rw [Isotope.Elgot.LawfulElgotMonad.fixpoint]
    have hlocal : LambdaSSA.At (List.ofFn (fun _ : Fin 1 => X)) 0 X := by
      simp [LambdaSSA.At]
    have hsum : (Sum.inl x : LabelValue (List.ofFn fun _ : Fin 1 => X)) =
        LabelValue.inject 0 hlocal x := by
      have hof : List.ofFn (fun _ : Fin 1 => X) = [X] := by simp
      cases hof
      rfl
    rw [hsum]
    dsimp only
    have hfinite := labelDenToFinite_recursiveInject
      (fun _ : Fin 1 => X) (0 : Fin 1) hlocal x
    have hvalue :
        (labelDenToFinite (fun _ : Fin 1 => X)
          (LabelValue.inject 0 hlocal x)).2 = x := by
      exact congrArg (fun z : FiniteLabelDen (fun _ : Fin 1 => X) => z.2)
        hfinite
    have hcollect : collective
        (ρ, labelDenToFinite (fun _ : Fin 1 => X)
          (LabelValue.inject 0 hlocal x)) =
        (g (ρ, x) >>= fun a =>
          pure (labelInject (result + 1) (at_succ hout) a)) := by
      unfold collective
      simp only [hvalue, labelInject_eq_recursive]
      apply bind_congr
      intro a
      congr
    rw [hcollect]
    simp only [LawfulMonad.bind_assoc]
    change _ = (g (ρ, x) >>= fun a => pure
      (labelInject (result + 1) (at_succ hout) a)) >>= fun next => _
    conv_rhs => rw [LawfulMonad.bind_assoc]
    apply bind_congr
    intro a
    rw [LawfulMonad.pure_bind]
    simp only [labelInject_eq_recursive]
    generalize_proofs hexternal
    have hre := LabelValue.appendSplit_ofFn_one_inject_external
      L X result hout hexternal a
    rw [LawfulMonad.pure_bind]
    exact (congrArg (Sum.elim pure _) hre).symm

theorem let₁_case_denotes [LawfulTypeModel τ]
    {β : LambdaIter.LocallyNameless.BoundCtx τ n}
    {e : ANF.Atom Empty Φ n} {left right body : ANF.Program Empty Φ (n + 1)}
    {X Y Z A C : τ}
    (he : ANF.Subtyping.Atom.HasType (Ctx.nil : Ctx Empty τ) β e (coprod X Y))
    (hl : ANF.Subtyping.Program.HasType (Ctx.nil : Ctx Empty τ) (β.snoc X) left Z)
    (hr : ANF.Subtyping.Program.HasType (Ctx.nil : Ctx Empty τ) (β.snoc Y) right Z)
    (hb : ANF.Subtyping.Program.HasType (Ctx.nil : Ctx Empty τ) (β.snoc Z) body A)
    (hAC : Subty A C) (sl : ToSSA.SimpleProgram left) (sr : ToSSA.SimpleProgram right)
    (sb : ToSSA.SimpleProgram body) {L : LambdaSSA.LCtx τ} {result : Nat}
    (hout : LambdaSSA.At L result C)
    (dl : Isotope.LambdaSSA.Subtyping.Semantics.Monadic.RegionDenotes ε
      (simpleProgram_hasType (L := Z :: L) sl hl (Subty.refl Z) (result := 0)
        (by simp [LambdaSSA.At]))
      (resultEval (ε := ε) (m := m) (L := Z :: L) hl (Subty.refl Z)
        (result := 0) (by simp [LambdaSSA.At])))
    (dr : Isotope.LambdaSSA.Subtyping.Semantics.Monadic.RegionDenotes ε
      (simpleProgram_hasType (L := Z :: L) sr hr (Subty.refl Z) (result := 0)
        (by simp [LambdaSSA.At]))
      (resultEval (ε := ε) (m := m) (L := Z :: L) hr (Subty.refl Z)
        (result := 0) (by simp [LambdaSSA.At])))
    (db : Isotope.LambdaSSA.Subtyping.Semantics.Monadic.RegionDenotes ε
      (simpleProgram_hasType (L := Z :: L) sb hb hAC (ToSSA.at_succ hout))
      (resultEval (ε := ε) (m := m) (L := Z :: L) hb hAC
        (ToSSA.at_succ hout))) :
    Isotope.LambdaSSA.Subtyping.Semantics.Monadic.RegionDenotes ε
      (simpleProgram_hasType (.let₁ (.case e sl sr) sb)
        (.let₁ (.case he hl hr) hb) hAC hout)
      (resultEval (ε := ε) (m := m) (.let₁ (.case he hl hr) hb) hAC hout) := by
  let hcase : ANF.Subtyping.Instr.HasType (Ctx.nil : Ctx Empty τ) β
      (.case e left right) Z := .case he hl hr
  have de : Isotope.LambdaSSA.Subtyping.Semantics.Monadic.RegionDenotes ε
      (LambdaSSA.Subtyping.Region.HasType.case (atom_hasType he)
        (simpleProgram_hasType (L := Z :: L) sl hl (Subty.refl Z) (result := 0)
          (by simp [LambdaSSA.At]))
        (simpleProgram_hasType (L := Z :: L) sr hr (Subty.refl Z) (result := 0)
          (by simp [LambdaSSA.At])))
      (fun ρ => ANF.Subtyping.denoteInstr (m := m) (ε := ε) hcase PUnit.unit
        (envToBound ρ) >>= fun z =>
          pure (labelInject (L := Z :: L) 0 (by simp [LambdaSSA.At]) z)) := by
    unfold resultEval at dl dr
    have dc := Isotope.LambdaSSA.Subtyping.Semantics.Monadic.RegionDenotes.case
      (atom_denotes (ε := ε) (m := m) he) dl dr
    convert dc using 1
    funext ρ
    simp only [hcase, ANF.Subtyping.denoteInstr, LawfulMonad.bind_assoc]
    apply bind_congr
    intro e'
    split <;> rename_i heq <;> rw [heq] <;>
      rw [show coeSub (Subty.refl Z) = id from LawfulTypeModel.coe_refl Z] <;>
      simp only [id_eq, LawfulMonad.pure_bind, envToBound_snoc]
  unfold resultEval at db
  have db' : Isotope.LambdaSSA.Subtyping.Semantics.Monadic.RegionDenotes ε
      (simpleProgram_hasType (L := Z :: L) sb hb hAC (ToSSA.at_succ hout))
      (fun ρ => (ANF.Subtyping.denoteProgram (m := m) (ε := ε) hb PUnit.unit
        (envToBound ρ) >>= fun a => pure (coeSub hAC a)) >>= fun c =>
          pure (labelInject (result + 1) (ToSSA.at_succ hout) c)) := by
    simpa only [LawfulMonad.bind_assoc] using db
  have dcfg := cfgOne_denotes (ε := ε) (m := m) (X := Z)
    (f := fun ρ => ANF.Subtyping.denoteInstr (m := m) (ε := ε) hcase
      PUnit.unit (envToBound ρ))
    (g := fun ρ => ANF.Subtyping.denoteProgram (m := m) (ε := ε) hb
      PUnit.unit (envToBound ρ) >>= fun a => pure (coeSub hAC a))
    (LambdaSSA.Subtyping.Region.HasType.case (atom_hasType he)
      (simpleProgram_hasType (L := Z :: L) sl hl (Subty.refl Z) (result := 0)
        (by simp [LambdaSSA.At]))
      (simpleProgram_hasType (L := Z :: L) sr hr (Subty.refl Z) (result := 0)
        (by simp [LambdaSSA.At])))
    (simpleProgram_hasType (L := Z :: L) sb hb hAC (ToSSA.at_succ hout)) hout de db'
  rw [simpleProgram_hasType]
  unfold resultEval at dcfg ⊢
  simpa only [hcase, ANF.Subtyping.denoteProgram, ANF.Subtyping.denoteInstr,
    LawfulMonad.bind_assoc] using dcfg

theorem let₂_denotes {β : LambdaIter.LocallyNameless.BoundCtx τ n}
    {a : ANF.Atom Empty Φ n} {body : ANF.Program Empty Φ (n + 2)}
    {X Y A C : τ}
    (ha : ANF.Subtyping.Atom.HasType (Ctx.nil : Ctx Empty τ) β a (tensor X Y))
    (hb : ANF.Subtyping.Program.HasType (Ctx.nil : Ctx Empty τ)
      ((β.snoc X).snoc Y) body A) (hAC : Subty A C)
    (hs : ToSSA.SimpleProgram body) {L : LambdaSSA.LCtx τ} {result : Nat}
    (hout : LambdaSSA.At L result C)
    (db : Isotope.LambdaSSA.Subtyping.Semantics.Monadic.RegionDenotes ε
      (simpleProgram_hasType hs hb hAC hout)
      (resultEval (ε := ε) (m := m) hb hAC hout)) :
    Isotope.LambdaSSA.Subtyping.Semantics.Monadic.RegionDenotes ε
      (simpleProgram_hasType (.let₂ hs) (.let₂ ha hb) hAC hout)
      (resultEval (ε := ε) (m := m) (.let₂ ha hb) hAC hout) := by
  rw [simpleProgram_hasType]
  unfold resultEval at db ⊢
  simpa only [ANF.Subtyping.denoteProgram, LawfulMonad.bind_assoc] using
    (Isotope.LambdaSSA.Subtyping.Semantics.Monadic.RegionDenotes.let₂
      (atom_denotes (ε := ε) (m := m) ha) db)

end Isotope.LambdaSSA.Translation.ANF.ToSSA.Subtyping
