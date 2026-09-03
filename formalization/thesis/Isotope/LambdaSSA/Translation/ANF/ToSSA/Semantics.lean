import Isotope.LambdaSSA.Translation.ANF.ToSSA
import Isotope.LambdaSSA.Semantics.Monadic.Region
import Isotope.LambdaIter.Semantics.Denotation

/-! # Monadic correctness of ANF to lambda-SSA compilation -/

namespace Isotope.LambdaSSA.Translation.ANF.ToSSA

set_option relaxedAutoImplicit true

open Isotope.LambdaIter
open Isotope.LambdaIter.Subtyping.Semantics
open Isotope.LambdaSSA.Semantics.Monadic

universe u v q r

variable {τ : Type u} [TypeFormers τ] [Subtyping τ] [TypeModel.{u, v} τ]
variable {Φ : Type q} [HasTy Φ τ]
variable {ε : Type r} [HasEff Φ ε] [Bot ε]
variable {m : Type v → Type v} [Monad m] [LawfulMonad m]
variable [Isotope.Elgot.Iterate m] [Isotope.Elgot.LawfulElgotMonad m]
variable [Isotope.LambdaIter.Subtyping.Semantics.InstructionModel Φ τ ε m]

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
    Env.get ρ i.val
        (LambdaSSA.LocallyNameless.ToDeBruijn.getElem_context β i) =
      BoundDen.get (envToBound ρ) i := by
  induction β with
  | nil => exact Fin.elim0 i
  | snoc β A ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · simpa [Env.get, BoundDen.get] using ih ρ.1 j

/-- Compiling an ANF atom preserves its direct monadic term denotation. -/
theorem atom_denotes {β : LambdaIter.LocallyNameless.BoundCtx τ n}
    {a : Atom Empty Φ n} {A : τ}
    (h : Atom.HasType (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty τ) β a A) :
    Isotope.LambdaSSA.Semantics.Monadic.Denotes ε (atom_hasType h) (fun ρ =>
      Isotope.LambdaIter.Semantics.denote (ε := ε) (m := m)
        h.toLambdaIter PUnit.unit (envToBound ρ)) := by
  induction h with
  | fv h => cases h
  | bv => simpa [LambdaIter.Semantics.denote, Atom.HasType.toLambdaIter,
      envToBound, env_get_context] using
      (Denotes.var (τ := τ) (Φ := Φ) (ε := ε) (m := m)
        (LambdaSSA.LocallyNameless.ToDeBruijn.getElem_context _ _))
  | op _ ih => exact .op ih
  | unit => exact Denotes.unit (ε := ε) (m := m)
  | pair _ _ iha ihb => exact .pair iha ihb
  | inl _ ih => exact .inl ih
  | inr _ ih => exact .inr ih
  | abort _ ih => exact .abort ih

/-- Direct source evaluation followed by the distinguished SSA result label. -/
noncomputable def resultEval {β : LambdaIter.LocallyNameless.BoundCtx τ n}
    {p : Program Empty Φ n} {A : τ}
    (h : Program.HasType (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty τ) β p A)
    {L : LambdaSSA.LCtx τ} {result : Nat} (hout : LambdaSSA.At L result A) :
    Env (LambdaSSA.LocallyNameless.ToDeBruijn.context β) → m (LabelDen L) :=
  fun ρ => LambdaIter.Semantics.denote (ε := ε) (m := m)
    h.toLambdaIter PUnit.unit (envToBound ρ) >>= fun a =>
      pure (labelInject result hout a)

/-- The return instruction is compiled to exactly one typed branch. -/
theorem ret_denotes {β : LambdaIter.LocallyNameless.BoundCtx τ n}
    {a : Atom Empty Φ n} {A : τ}
    (ha : Atom.HasType (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty τ) β a A)
    {L : LambdaSSA.LCtx τ} {result : Nat} (hout : LambdaSSA.At L result A) :
    RegionDenotes ε
      (simpleProgram_hasType (.ret a) (.ret ha) hout)
      (resultEval (ε := ε) (m := m) (.ret ha) hout) := by
  unfold resultEval
  simpa [LambdaIter.Semantics.denote,
    Program.HasType.toLambdaIter] using
    (RegionDenotes.br (h := hout) (atom_denotes (ε := ε) (m := m) ha))

/-- A one-block CFG whose entry always transfers to its block and whose block
always transfers to an external continuation contracts to their sequential
composition. -/
theorem cfgOne_denotes
    {Γ : LambdaSSA.VCtx τ} {L : LambdaSSA.LCtx τ} {X A : τ}
    {entry block : LambdaSSA.Region Φ}
    (he : LambdaSSA.Region.HasType Γ entry (X :: L))
    (hb : LambdaSSA.Region.HasType (X :: Γ) block (X :: L))
    {f : Env Γ → m (TyDen X)}
    {g : Env (X :: Γ) → m (TyDen A)}
    {result : Nat} (hout : LambdaSSA.At L result A)
    (de : RegionDenotes ε he (fun ρ => f ρ >>= fun x =>
      pure (labelInject 0 (by simp [LambdaSSA.At]) x)))
    (db : RegionDenotes ε hb (fun ρ => g ρ >>= fun a =>
      pure (labelInject (result + 1) (at_succ hout) a))) :
    RegionDenotes ε
      (LambdaSSA.Region.HasType.cfg (fun _ : Fin 1 => X) he (fun _ => hb))
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
  have dcfg := RegionDenotes.cfg (R := fun _ : Fin 1 => X)
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

/-- The atomic-let compilation step preserves the result-passing relation. -/
theorem let₁_atom_denotes
    {β : LambdaIter.LocallyNameless.BoundCtx τ n}
    {a : Atom Empty Φ n} {body : Program Empty Φ (n + 1)} {X A : τ}
    (ha : Atom.HasType (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty τ) β a X)
    (hb : Program.HasType (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty τ)
      (β.snoc X) body A)
    (hs : SimpleProgram body)
    {L : LambdaSSA.LCtx τ} {result : Nat} (hout : LambdaSSA.At L result A)
    (db : RegionDenotes ε (simpleProgram_hasType hs hb hout)
      (resultEval (ε := ε) (m := m) hb hout)) :
    RegionDenotes ε
      (simpleProgram_hasType (.let₁ (.atom a) hs) (.let₁ (.atom ha) hb) hout)
      (resultEval (ε := ε) (m := m) (.let₁ (.atom ha) hb) hout) := by
  unfold resultEval
  unfold resultEval at db
  simpa [LambdaIter.Semantics.denote,
    Program.HasType.toLambdaIter, Instr.HasType.toLambdaIter,
    LawfulMonad.bind_assoc] using
    (RegionDenotes.let₁ (atom_denotes (ε := ε) (m := m) ha) db)

/-- The case-instruction compilation step preserves the result-passing
relation by contracting the fresh join block. -/
theorem let₁_case_denotes
    {β : LambdaIter.LocallyNameless.BoundCtx τ n}
    {e : Atom Empty Φ n}
    {left right : Program Empty Φ (n + 1)}
    {body : Program Empty Φ (n + 1)} {X Y Z A : τ}
    (he : Atom.HasType (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty τ) β e
      (LambdaIter.coprod X Y))
    (hl : Program.HasType (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty τ)
      (β.snoc X) left Z)
    (hr : Program.HasType (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty τ)
      (β.snoc Y) right Z)
    (hb : Program.HasType (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty τ)
      (β.snoc Z) body A)
    (sl : SimpleProgram left) (sr : SimpleProgram right) (sb : SimpleProgram body)
    {L : LambdaSSA.LCtx τ} {result : Nat} (hout : LambdaSSA.At L result A)
    (dl : RegionDenotes ε (simpleProgram_hasType (L := Z :: L) sl hl (result := 0)
      (by simp [LambdaSSA.At]))
      (resultEval (ε := ε) (m := m) (L := Z :: L) (result := 0)
        hl (by simp [LambdaSSA.At])))
    (dr : RegionDenotes ε (simpleProgram_hasType (L := Z :: L) sr hr (result := 0)
      (by simp [LambdaSSA.At]))
      (resultEval (ε := ε) (m := m) (L := Z :: L) (result := 0)
        hr (by simp [LambdaSSA.At])))
    (db : RegionDenotes ε (simpleProgram_hasType (L := Z :: L) sb hb (at_succ hout))
      (resultEval (ε := ε) (m := m) (L := Z :: L) hb (at_succ hout))) :
    RegionDenotes ε
      (simpleProgram_hasType (.let₁ (.case e sl sr) sb)
        (.let₁ (.case he hl hr) hb) hout)
      (resultEval (ε := ε) (m := m) (.let₁ (.case he hl hr) hb) hout) := by
  let hcase : Instr.HasType (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty τ) β
      (.case e left right) Z := .case he hl hr
  have de : RegionDenotes ε
      (LambdaSSA.Region.HasType.case (atom_hasType he)
        (simpleProgram_hasType (L := Z :: L) sl hl (result := 0)
          (by simp [LambdaSSA.At]))
        (simpleProgram_hasType (L := Z :: L) sr hr (result := 0)
          (by simp [LambdaSSA.At])))
      (fun ρ => LambdaIter.Semantics.denote (ε := ε) (m := m)
        hcase.toLambdaIter PUnit.unit (envToBound ρ) >>= fun z =>
          pure (labelInject (L := Z :: L) 0 (by simp [LambdaSSA.At]) z)) := by
    unfold resultEval at dl dr
    have dc := RegionDenotes.case
      (atom_denotes (ε := ε) (m := m) he) dl dr
    convert dc using 1
    funext ρ
    simp only [hcase, LambdaIter.Semantics.denote,
      Instr.HasType.toLambdaIter, LawfulMonad.bind_assoc]
    apply bind_congr
    intro e'
    split <;> rename_i heq <;> rw [heq] <;> congr
  have dcfg := cfgOne_denotes (ε := ε) (m := m) (X := Z)
    (LambdaSSA.Region.HasType.case (atom_hasType he)
      (simpleProgram_hasType (L := Z :: L) sl hl (result := 0)
        (by simp [LambdaSSA.At]))
      (simpleProgram_hasType (L := Z :: L) sr hr (result := 0)
        (by simp [LambdaSSA.At])))
    (simpleProgram_hasType (L := Z :: L) sb hb (at_succ hout)) hout de db
  unfold resultEval
  unfold resultEval at dcfg
  simpa [hcase, LambdaIter.Semantics.denote, Program.HasType.toLambdaIter,
    Instr.HasType.toLambdaIter, LawfulMonad.bind_assoc] using dcfg

/-- The pair-destructuring compilation step preserves the result-passing relation. -/
theorem let₂_denotes
    {β : LambdaIter.LocallyNameless.BoundCtx τ n}
    {a : Atom Empty Φ n} {body : Program Empty Φ (n + 2)} {X Y A : τ}
    (ha : Atom.HasType (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty τ) β a
      (LambdaIter.tensor X Y))
    (hb : Program.HasType (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty τ)
      ((β.snoc X).snoc Y) body A)
    (hs : SimpleProgram body)
    {L : LambdaSSA.LCtx τ} {result : Nat} (hout : LambdaSSA.At L result A)
    (db : RegionDenotes ε (simpleProgram_hasType hs hb hout)
      (resultEval (ε := ε) (m := m) hb hout)) :
    RegionDenotes ε
      (simpleProgram_hasType (.let₂ hs) (.let₂ ha hb) hout)
      (resultEval (ε := ε) (m := m) (.let₂ ha hb) hout) := by
  unfold resultEval
  unfold resultEval at db
  simpa [LambdaIter.Semantics.denote,
    Program.HasType.toLambdaIter, LawfulMonad.bind_assoc] using
    (RegionDenotes.let₂ (atom_denotes (ε := ε) (m := m) ha) db)

end Isotope.LambdaSSA.Translation.ANF.ToSSA
