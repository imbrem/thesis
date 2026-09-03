import Isotope.LambdaSSA.Translation.ANF.ToSSA.Subtyping.Semantics
import Isotope.LambdaSSA.Translation.ANF.ToSSA.SemanticsIter
import Isotope.LambdaSSA.Subtyping.Semantics.Monadic.Renaming

/-! # Two-block CFG correctness for proof-relevant ANF iteration -/

namespace Isotope.LambdaSSA.Translation.ANF.ToSSA.Subtyping

set_option relaxedAutoImplicit true

open Isotope.LambdaIter
open Isotope.LambdaIter.Subtyping.Semantics
open Isotope.LambdaSSA.Translation.ANF
open Isotope.LambdaSSA.Semantics.Monadic

universe u v q r

variable {τ : Type u} [TypeFormers τ] [LambdaIter.Subtyping τ]
  [TypeModel.{u, v} τ] [LawfulTypeModel τ]
variable {Φ : Type q} [HasTy Φ τ]
variable {ε : Type r} [HasEff Φ ε] [Bot ε]
variable {m : Type v → Type v} [Monad m] [LawfulMonad m]
variable [Isotope.Elgot.Iterate m] [Isotope.Elgot.LawfulElgotMonad m]
variable [InstructionModel Φ τ ε m]

private def cfgTypingData {Γ : LambdaSSA.VCtx τ} {L : LambdaSSA.LCtx τ}
    {entry : LambdaSSA.Region Φ} {n : Nat}
    {blocks : Fin n → LambdaSSA.Region Φ} :
    LambdaSSA.Subtyping.Region.HasType Γ (.cfg entry n blocks) L →
      Σ R : Fin n → τ,
        LambdaSSA.Subtyping.Region.HasType Γ entry (List.ofFn R ++ L) ×
          (∀ i, LambdaSSA.Subtyping.Region.HasType (R i :: Γ) (blocks i)
            (List.ofFn R ++ L))
  | .cfg R he hb => ⟨R, he, hb⟩

private theorem cfgTypingData_eta {Γ : LambdaSSA.VCtx τ} {L : LambdaSSA.LCtx τ}
    {entry : LambdaSSA.Region Φ} {n : Nat}
    {blocks : Fin n → LambdaSSA.Region Φ}
    (h : LambdaSSA.Subtyping.Region.HasType Γ (.cfg entry n blocks) L) :
    let d := cfgTypingData h
    LambdaSSA.Subtyping.Region.HasType.cfg d.1 d.2.1 d.2.2 = h := by
  cases h <;> rfl

private theorem cfgTypingData_cast_eta
    {Γ : LambdaSSA.VCtx τ} {L : LambdaSSA.LCtx τ}
    {entry : LambdaSSA.Region Φ} {n : Nat}
    {blocks : Fin n → LambdaSSA.Region Φ}
    (h : LambdaSSA.Subtyping.Region.HasType Γ (.cfg entry n blocks) L)
    (R : Fin n → τ) (hR : (cfgTypingData h).1 = R) :
    LambdaSSA.Subtyping.Region.HasType.cfg R
      (hR ▸ (cfgTypingData h).2.1) (hR ▸ (cfgTypingData h).2.2) = h := by
  subst R
  exact cfgTypingData_eta h

theorem let₁_iter_denotes
    {β : LambdaIter.LocallyNameless.BoundCtx τ n}
    {init : ANF.Atom Empty Φ n} {loop : ANF.Program Empty Φ (n + 1)}
    {body : ANF.Program Empty Φ (n + 1)} {X Y A C : τ}
    (hinit : ANF.Subtyping.Atom.HasType
      (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty τ) β init X)
    (hloop : ANF.Subtyping.Program.HasType
      (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty τ)
      (β.snoc X) loop (LambdaIter.coprod Y X))
    (hbody : ANF.Subtyping.Program.HasType
      (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty τ) (β.snoc Y) body A)
    (hAC : Subty A C) (sloop : ToSSA.SimpleProgram loop)
    (sbody : ToSSA.SimpleProgram body)
    {L : LambdaSSA.LCtx τ} {result : Nat} (hout : LambdaSSA.At L result C)
    (dloop : Isotope.LambdaSSA.Subtyping.Semantics.Monadic.RegionDenotes ε
      (simpleProgram_hasType (L := X :: LambdaIter.coprod Y X :: L)
        sloop hloop (Subty.refl _) (result := 1) (by simp [LambdaSSA.At]))
      (resultEval (ε := ε) (m := m)
        (L := X :: LambdaIter.coprod Y X :: L) hloop (Subty.refl _)
        (result := 1) (by simp [LambdaSSA.At])))
    (dbody : Isotope.LambdaSSA.Subtyping.Semantics.Monadic.RegionDenotes ε
      (simpleProgram_hasType (L := X :: LambdaIter.coprod Y X :: L)
        sbody hbody hAC (result := result + 2)
        (by simpa [LambdaSSA.At] using hout))
      (resultEval (ε := ε) (m := m)
        (L := X :: LambdaIter.coprod Y X :: L) hbody hAC
        (result := result + 2) (by simpa [LambdaSSA.At] using hout))) :
    Isotope.LambdaSSA.Subtyping.Semantics.Monadic.RegionDenotes ε
      (simpleProgram_hasType (.let₁ (.iter init sloop) sbody)
        (.let₁ (.iter hinit hloop) hbody) hAC hout)
      (resultEval (ε := ε) (m := m)
        (.let₁ (.iter hinit hloop) hbody) hAC hout) := by
  let Γ := LambdaSSA.LocallyNameless.ToDeBruijn.context β
  let Z := LambdaIter.coprod Y X
  generalize htopdef : simpleProgram_hasType (.let₁ (.iter init sloop) sbody)
    (.let₁ (.iter hinit hloop) hbody) hAC hout = htop
  cases htop
  rename_i R hentry hblocks
  have hR : R = ToSSA.twoLabels X Z := by
    have hr := congrArg (fun h => (cfgTypingData h).1) htopdef
    dsimp only [cfgTypingData] at hr
    rw [simpleProgram_hasType.eq_def] at hr
    exact hr.symm
  subst R
  have hdata := congrArg (fun h => cfgTypingData h) htopdef
  rw [simpleProgram_hasType.eq_def] at hdata
  cases hdata
  let R := ToSSA.twoLabels X Z
  let finit : Env Γ → m (TyDen X) := fun ρ =>
    ANF.Subtyping.denoteAtom (ε := ε) (m := m) hinit PUnit.unit
      (envToBound ρ)
  let floop : Env (X :: Γ) → m (TyDen Z) := fun ρ =>
    ANF.Subtyping.denoteProgram (ε := ε) (m := m) hloop PUnit.unit
      (envToBound ρ)
  let fbody : Env (Y :: Γ) → m (TyDen C) := fun ρ =>
    ANF.Subtyping.denoteProgram (ε := ε) (m := m) hbody PUnit.unit
      (envToBound ρ) >>= fun a => pure (coeSub hAC a)
  have de : Isotope.LambdaSSA.Subtyping.Semantics.Monadic.RegionDenotes ε
      (LambdaSSA.Subtyping.Region.HasType.br
        (L := List.ofFn R ++ L) (A := X) (ℓ := 0)
        (by simp [R, Z, ToSSA.ofFn_twoLabels, LambdaSSA.At])
        (atom_hasType hinit))
      (fun ρ => finit ρ >>= fun x =>
        pure (labelInject (L := List.ofFn R ++ L) 0
          (by simp [R, Z, ToSSA.ofFn_twoLabels, LambdaSSA.At]) x)) := by
    exact Isotope.LambdaSSA.Subtyping.Semantics.Monadic.RegionDenotes.br
      (atom_denotes (ε := ε) (m := m) hinit)
  have dloop' : Isotope.LambdaSSA.Subtyping.Semantics.Monadic.RegionDenotes ε
      (simpleProgram_hasType (L := List.ofFn R ++ L) sloop hloop
        (Subty.refl Z) (result := 1)
        (by simp [R, Z, ToSSA.ofFn_twoLabels, LambdaSSA.At]))
      (fun ρ => floop ρ >>= fun z =>
        pure (labelInject (L := List.ofFn R ++ L) 1
          (by simp [R, Z, ToSSA.ofFn_twoLabels, LambdaSSA.At]) z)) := by
    unfold resultEval at dloop
    rw [show coeSub (Subty.refl Z) = id from LawfulTypeModel.coe_refl Z] at dloop
    simpa only [R, Z, floop, ToSSA.ofFn_twoLabels, id_eq,
      LawfulMonad.pure_bind] using dloop
  have dbody' : Isotope.LambdaSSA.Subtyping.Semantics.Monadic.RegionDenotes ε
      ((simpleProgram_hasType (L := List.ofFn R ++ L) sbody hbody hAC
        (result := result + 2)
        (by simp [R, Z, ToSSA.ofFn_twoLabels, LambdaSSA.At]; exact hout)).renameVars
          ((LambdaSSA.Ren.wk Γ Z).lift Y))
      (fun ρ : Env (Y :: Z :: Γ) => fbody (ρ.1.1, ρ.2) >>= fun c =>
        pure (labelInject (L := List.ofFn R ++ L) (result + 2)
          (by simp [R, Z, ToSSA.ofFn_twoLabels, LambdaSSA.At]; exact hout) c)) := by
    have d := dbody.renameVars ((LambdaSSA.Ren.wk Γ Z).lift Y)
    have henv (ρ : Env (Y :: Z :: Γ)) :
        Env.rename ((LambdaSSA.Ren.wk Γ Z).lift Y) ρ = (ρ.1.1, ρ.2) := by
      rcases ρ with ⟨⟨γ, z⟩, y⟩
      exact (Env.rename_lift (LambdaSSA.Ren.wk Γ Z) (γ, z) Y y).trans
        (congrArg (fun δ => (δ, y)) (ToSSA.envRename_wk Γ Z (γ, z)))
    unfold resultEval at d
    simpa only [R, Z, fbody, ToSSA.ofFn_twoLabels, henv,
      LawfulMonad.bind_assoc] using d
  have hlabel0 : LambdaSSA.At (List.ofFn R ++ L) 0 X := by
    simp [R, Z, ToSSA.ofFn_twoLabels, LambdaSSA.At]
  have hvarX : LambdaSSA.At (X :: Z :: Γ) 0 X := by simp [LambdaSSA.At]
  have drecur : Isotope.LambdaSSA.Subtyping.Semantics.Monadic.RegionDenotes ε
      (LambdaSSA.Subtyping.Region.HasType.br
        (Γ := X :: Z :: Γ) (L := List.ofFn R ++ L) (A := X) (ℓ := 0)
        hlabel0 (.var (Φ := Φ) (i := 0) hvarX))
      (fun ρ => (pure (labelInject (L := List.ofFn R ++ L) 0 hlabel0 ρ.2) :
        m (LabelDen (List.ofFn R ++ L)))) := by
    simpa [Env.get] using
      (Isotope.LambdaSSA.Subtyping.Semantics.Monadic.RegionDenotes.br
        (ε := ε) (m := m) (h := hlabel0)
        (Isotope.LambdaSSA.Subtyping.Semantics.Monadic.Denotes.var
          (Φ := Φ) (ε := ε) (m := m) hvarX))
  have hvarZ : LambdaSSA.At (Z :: Γ) 0 Z := by simp [LambdaSSA.At]
  have dcase : Isotope.LambdaSSA.Subtyping.Semantics.Monadic.RegionDenotes ε
      (LambdaSSA.Subtyping.Region.HasType.case
        (Γ := Z :: Γ) (L := List.ofFn R ++ L) (A := Y) (B := X)
        (.var (Φ := Φ) hvarZ)
        ((simpleProgram_hasType (L := List.ofFn R ++ L) sbody hbody hAC
          (result := result + 2)
          (by simp [R, Z, ToSSA.ofFn_twoLabels, LambdaSSA.At]; exact hout)).renameVars
            ((LambdaSSA.Ren.wk Γ Z).lift Y))
        (LambdaSSA.Subtyping.Region.HasType.br hlabel0
          (.var (Φ := Φ) hvarX)))
      (fun ρ => match TypeModel.coprodEquiv Y X ρ.2 with
        | .inl y => fbody (ρ.1, y) >>= fun c =>
            pure (labelInject (L := List.ofFn R ++ L) (result + 2)
              (by simp [R, Z, ToSSA.ofFn_twoLabels, LambdaSSA.At]; exact hout) c)
        | .inr x => pure (labelInject (L := List.ofFn R ++ L) 0
            hlabel0 x)) := by
    convert Isotope.LambdaSSA.Subtyping.Semantics.Monadic.RegionDenotes.case
      (Isotope.LambdaSSA.Subtyping.Semantics.Monadic.Denotes.var
        (Φ := Φ) (ε := ε) (m := m) hvarZ) dbody' drecur using 1
    funext ρ
    simp only [Env.get, LawfulMonad.pure_bind]
    cases TypeModel.coprodEquiv Y X ρ.2 <;> rfl
  let collective : Env Γ × FiniteLabelDen R →
      m (LabelDen (List.ofFn R ++ L)) := fun p =>
    Fin.cases (fun x => floop (p.1, x) >>= fun z =>
      pure (labelInject (L := List.ofFn R ++ L) 1
        (by simp [R, Z, ToSSA.ofFn_twoLabels, LambdaSSA.At]) z))
      (fun j => Fin.cases (fun z =>
        match TypeModel.coprodEquiv Y X z with
        | .inl y => fbody (p.1, y) >>= fun c =>
            pure (labelInject (L := List.ofFn R ++ L) (result + 2)
              (by simp [R, Z, ToSSA.ofFn_twoLabels, LambdaSSA.At]; exact hout) c)
        | .inr x => pure (labelInject (L := List.ofFn R ++ L) 0
            (by simp [R, Z, ToSSA.ofFn_twoLabels, LambdaSSA.At]) x))
        (fun k => Fin.elim0 k) j) p.2.1 p.2.2
  have dc : CollectiveDenotes Γ R L
      (fun i => Fin.cases (fun ρ => floop ρ >>= fun z =>
          pure (labelInject (L := List.ofFn R ++ L) 1
            (by simp [R, Z, ToSSA.ofFn_twoLabels, LambdaSSA.At]) z))
        (fun j => Fin.cases (fun ρ => match TypeModel.coprodEquiv Y X ρ.2 with
          | .inl y => fbody (ρ.1, y) >>= fun c =>
              pure (labelInject (L := List.ofFn R ++ L) (result + 2)
                (by simp [R, Z, ToSSA.ofFn_twoLabels, LambdaSSA.At]; exact hout) c)
          | .inr x => pure (labelInject (L := List.ofFn R ++ L) 0
              (by simp [R, Z, ToSSA.ofFn_twoLabels, LambdaSSA.At]) x))
          (fun k => Fin.elim0 k) j) i) collective := by
    constructor
    intro i ρ a
    fin_cases i <;> rfl
  simp only [R, Z, Γ] at dloop' dcase dc ⊢
  let he := LambdaSSA.Subtyping.Region.HasType.br
    (L := List.ofFn R ++ L) (A := X) (ℓ := 0)
    (by simp [R, Z, ToSSA.twoLabels, LambdaSSA.At]) (atom_hasType hinit)
  let hb : ∀ i, LambdaSSA.Subtyping.Region.HasType
      (R i :: LambdaSSA.LocallyNameless.ToDeBruijn.context β)
      ((fun i => Fin.cases (ToSSA.simpleProgram 1 sloop)
        (fun j => Fin.cases
          (.case (.var 0)
            ((ToSSA.simpleProgram (result + 2) sbody).renameVars
              (LambdaSSA.lift Nat.succ))
            (.br 0 (.var 0)))
          (fun k => k.elim0) j) i) i) (List.ofFn R ++ L) := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa [R, Z, ToSSA.twoLabels] using
        simpleProgram_hasType sloop hloop (Subty.refl _)
          (result := 1) (by simp [LambdaSSA.At])
    · have hj : j = 0 := Subsingleton.elim _ _
      subst j
      simp only [R, Z, ToSSA.twoLabels]
      exact LambdaSSA.Subtyping.Region.HasType.case
        (LambdaSSA.Subtyping.Tm.HasType.var hvarZ)
        ((simpleProgram_hasType (L := List.ofFn R ++ L) sbody hbody hAC
          (result := result + 2)
          (by simp [R, Z, ToSSA.twoLabels, LambdaSSA.At]; exact hout)).renameVars
            ((LambdaSSA.Ren.wk Γ Z).lift Y))
        (LambdaSSA.Subtyping.Region.HasType.br hlabel0
          (LambdaSSA.Subtyping.Tm.HasType.var hvarX))
  have dcfg := Isotope.LambdaSSA.Subtyping.Semantics.Monadic.RegionDenotes.cfg
    (R := R) (collective := collective)
    (entry := .br 0 (ToSSA.atom init))
    (blocks := fun i => Fin.cases (ToSSA.simpleProgram 1 sloop)
      (fun j => Fin.cases
        (.case (.var 0)
          ((ToSSA.simpleProgram (result + 2) sbody).renameVars
            (LambdaSSA.lift Nat.succ))
          (.br 0 (.var 0)))
        (fun k => k.elim0) j) i)
    he hb (by simpa [he] using de) (fun i => Fin.cases
      (by
        simp only [Fin.cases_zero]
        convert dloop' using 1)
      (fun j => Fin.cases
        (by
          simp only [Fin.cases_succ, Fin.cases_zero]
          convert dcase using 1)
        (fun k => k.elim0) j) i) dc
  convert dcfg using 1
  · funext ρ
    unfold resultEval
    simp only [ANF.Subtyping.denoteProgram, ANF.Subtyping.denoteInstr,
      LawfulMonad.bind_assoc]
    let step : TyDen X → m (TyDen Y ⊕ TyDen X) := fun x =>
      floop (ρ, x) >>= fun z => pure (TypeModel.coprodEquiv Y X z)
    let k : TyDen Y → m (LabelDen L) := fun y =>
      fbody (ρ, y) >>= fun c => pure (labelInject result hout c)
    let phase : TyDen X ⊕ (TyDen Y ⊕ TyDen X) →
        m (LabelDen L ⊕ (TyDen X ⊕ (TyDen Y ⊕ TyDen X))) :=
      fun s => match s with
      | .inl x => step x >>= fun z => pure (Sum.inr (Sum.inr z))
      | .inr (.inl y) => k y >>= fun c => pure (Sum.inl c)
      | .inr (.inr x) => pure (Sum.inr (Sum.inl x))
    have hlocal0 : LambdaSSA.At (List.ofFn R) 0 X := by
      simp [R, Z, ToSSA.ofFn_twoLabels, LambdaSSA.At]
    have hlocal1 : LambdaSSA.At (List.ofFn R) 1 Z := by
      simp [R, Z, ToSSA.ofFn_twoLabels, LambdaSSA.At]
    let enc : TyDen X ⊕ (TyDen Y ⊕ TyDen X) → LabelDen (List.ofFn R) :=
      Sum.elim (LabelValue.inject 0 hlocal0)
        (fun z => LabelValue.inject 1 hlocal1
          ((TypeModel.coprodEquiv Y X).symm z))
    let actual : LabelDen (List.ofFn R) →
        m (LabelDen L ⊕ LabelDen (List.ofFn R)) := fun current =>
      collective (ρ, labelDenToFinite R current) >>= fun next =>
        pure (LabelValue.appendSplit (List.ofFn R) L next)
    have hcomm : Isotope.Elgot.kcomp phase
          (Isotope.Elgot.liftPure (m := m) (Sum.map id enc)) =
        Isotope.Elgot.kcomp (Isotope.Elgot.liftPure (m := m) enc) actual := by
      funext s
      cases s with
      | inl x =>
          dsimp only [phase, enc]
          simp only [phase, enc, Isotope.Elgot.kcomp, Isotope.Elgot.liftPure,
            LawfulMonad.pure_bind, Function.comp_apply, actual]
          change _ = (collective
            (ρ, labelDenToFinite R (LabelValue.inject 0 hlocal0 x)) >>= fun next =>
              pure (LabelValue.appendSplit (List.ofFn R) L next))
          rw [ToSSA.labelDenToFinite_two_zero X Z hlocal0 x]
          rw [dc.restrict 0 ρ x]
          simp only [Fin.cases_zero]
          simp [step, enc, R, Z, ToSSA.recursiveInject_two_one,
            ToSSA.appendSplit_two_inject_one, labelInject_eq_recursive,
            LawfulMonad.bind_assoc]
          rfl
      | inr z =>
          cases z with
          | inl y =>
              dsimp only [phase, enc]
              simp only [phase, enc, Isotope.Elgot.kcomp, Isotope.Elgot.liftPure,
                LawfulMonad.pure_bind, Function.comp_apply, actual]
              change _ = (collective
                (ρ, labelDenToFinite R (LabelValue.inject 1 hlocal1
                  ((TypeModel.coprodEquiv Y X).symm (Sum.inl y)))) >>= fun next =>
                  pure (LabelValue.appendSplit (List.ofFn R) L next))
              rw [ToSSA.labelDenToFinite_two_one X Z hlocal1
                ((TypeModel.coprodEquiv Y X).symm (Sum.inl y))]
              rw [dc.restrict 1 ρ
                ((TypeModel.coprodEquiv Y X).symm (Sum.inl y))]
              rw [ToSSA.finCases_two_one, Fin.cases_zero]
              simp [R, Z, phase, actual, enc, k, collective, LabelValue.inject,
                Fin.cases, Isotope.Elgot.kcomp, Isotope.Elgot.liftPure,
                ToSSA.appendSplit_two_inject_external, LawfulMonad.bind_assoc]
              apply congrArg (fun q => q <$> fbody (ρ, y))
              funext c
              exact (ToSSA.appendSplit_two_inject_external
                L X Z result hout _ c).symm
          | inr x =>
              dsimp only [phase, enc]
              simp only [phase, enc, Isotope.Elgot.kcomp, Isotope.Elgot.liftPure,
                LawfulMonad.pure_bind, Function.comp_apply, actual]
              change _ = (collective
                (ρ, labelDenToFinite R (LabelValue.inject 1 hlocal1
                  ((TypeModel.coprodEquiv Y X).symm (Sum.inr x)))) >>= fun next =>
                  pure (LabelValue.appendSplit (List.ofFn R) L next))
              rw [ToSSA.labelDenToFinite_two_one X Z hlocal1
                ((TypeModel.coprodEquiv Y X).symm (Sum.inr x))]
              rw [dc.restrict 1 ρ
                ((TypeModel.coprodEquiv Y X).symm (Sum.inr x))]
              rw [ToSSA.finCases_two_one, Fin.cases_zero]
              simp [R, Z, phase, actual, enc, collective, LabelValue.inject,
                Fin.cases, Isotope.Elgot.kcomp, Isotope.Elgot.liftPure,
                ToSSA.appendSplit_two_inject_zero]
              rfl
    have hu := Isotope.Elgot.LawfulElgotMonad.uniformity (m := m)
      phase actual enc hcomm
    have hphase : Isotope.Elgot.iter (m := m) phase =
        fun s => Isotope.Elgot.iter (m := m) actual (enc s) := by
      calc
        Isotope.Elgot.iter (m := m) phase =
            Isotope.Elgot.kcomp (Isotope.Elgot.liftPure (m := m) enc)
              (Isotope.Elgot.iter (m := m) actual) := hu
        _ = fun s => Isotope.Elgot.iter (m := m) actual (enc s) := by
          funext s
          simp [Isotope.Elgot.kcomp, Isotope.Elgot.liftPure]
    simp only [binaryCoproductIso_hom_labelAppendSplit]
    conv_lhs => enter [2, x, 2, y]; rw [← LawfulMonad.bind_assoc]
    change (finit ρ >>= fun x =>
      Isotope.Elgot.kcomp (Isotope.Elgot.iter (m := m) step) k x) = _
    rw [ToSSA.iter_effectful_two_phase step k]
    simp only [map_eq_pure_bind, LawfulMonad.bind_assoc,
      LawfulMonad.pure_bind]
    apply bind_congr
    intro x
    generalize_proofs hentry'
    have hr := ToSSA.appendSplit_two_inject_zero L X Z hentry' x
    split <;> rename_i hm
    · have hc := hr.symm.trans hm
      contradiction
    · have hc := Sum.inr.inj (hr.symm.trans hm)
      cases hc
      have henc : enc (Sum.inl x) = (Sum.inl x : LabelDen (List.ofFn R)) := by
        dsimp only [enc]
        simpa only [R] using ToSSA.recursiveInject_two_zero X Z hlocal0 x
      have hp := congrFun hphase (Sum.inl x)
      rw [henc] at hp
      simp only [phase, actual, LawfulMonad.bind_pure_comp] at hp ⊢
      convert hp using 1
      apply congrArg (fun q => Isotope.Elgot.iter (m := m) q (Sum.inl x))
      funext s
      cases s with
      | inl x => rfl
      | inr z => cases z <;> rfl

set_option maxRecDepth 4096 in
/-- Every simple proof-relevant ANF typing is preserved by structural SSA
compilation.  The result coercion is the exact source witness supplied by the
caller; only compiler-introduced join coercions are reflexive. -/
theorem simpleProgram_denotes
    {β : LambdaIter.LocallyNameless.BoundCtx τ n}
    {p : ANF.Program Empty Φ n} (hs : ToSSA.SimpleProgram p)
    {A C : τ}
    (h : ANF.Subtyping.Program.HasType
      (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty τ) β p A)
    (hAC : Subty A C) {L : LambdaSSA.LCtx τ} {result : Nat}
    (hout : LambdaSSA.At L result C) :
    Isotope.LambdaSSA.Subtyping.Semantics.Monadic.RegionDenotes ε
      (simpleProgram_hasType hs h hAC hout)
      (resultEval (ε := ε) (m := m) h hAC hout) := by
  cases hs with
  | ret a =>
      cases h with
      | ret ha => exact ret_denotes (ε := ε) (m := m) ha hAC hout
  | let₁ hi sb =>
      cases h with
      | let₁ hInstr hBody =>
        cases hi with
        | atom a =>
            cases hInstr with
            | atom ha =>
                exact let₁_atom_denotes (ε := ε) (m := m)
                  ha hBody hAC sb hout
                  (simpleProgram_denotes sb hBody hAC hout)
        | case e sl sr =>
            cases hInstr with
            | case he hl hr =>
                exact let₁_case_denotes (ε := ε) (m := m)
                  he hl hr hBody hAC sl sr sb hout
                  (simpleProgram_denotes sl hl (Subty.refl _)
                    (by simp [LambdaSSA.At]))
                  (simpleProgram_denotes sr hr (Subty.refl _)
                    (by simp [LambdaSSA.At]))
                  (simpleProgram_denotes sb hBody hAC (ToSSA.at_succ hout))
        | iter init sloop =>
            cases hInstr with
            | iter hinit hloop =>
                exact let₁_iter_denotes (ε := ε) (m := m)
                  hinit hloop hBody hAC sloop sb hout
                  (simpleProgram_denotes sloop hloop (Subty.refl _)
                    (by simp [LambdaSSA.At]))
                  (simpleProgram_denotes sb hBody hAC
                    (by simpa [LambdaSSA.At] using hout))
  | let₂ sb =>
      cases h with
      | let₂ ha hBody =>
          exact let₂_denotes (ε := ε) (m := m) ha hBody hAC sb hout
            (simpleProgram_denotes sb hBody hAC hout)
termination_by sizeOf p

/-- Semantic preservation for the public proof-relevant ANF-to-SSA compiler. -/
theorem program_denotes
    {β : LambdaIter.LocallyNameless.BoundCtx τ n}
    {p : ANF.Program Empty Φ n} {A : τ}
    (h : ANF.Subtyping.Program.HasType
      (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty τ) β p A)
    {L : LambdaSSA.LCtx τ} {result : Nat} (hout : LambdaSSA.At L result A) :
    Isotope.LambdaSSA.Subtyping.Semantics.Monadic.RegionDenotes ε
      (program_hasType h hout)
      (resultEval (ε := ε) (m := m) h (Subty.refl A) hout) :=
  simpleProgram_denotes (ToSSA.simpleProgram_all p) h (Subty.refl A) hout

end Isotope.LambdaSSA.Translation.ANF.ToSSA.Subtyping
