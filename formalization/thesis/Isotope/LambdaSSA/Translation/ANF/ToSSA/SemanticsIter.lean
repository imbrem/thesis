import Isotope.LambdaSSA.Translation.ANF.ToSSA.Semantics
import Isotope.LambdaSSA.Semantics.Monadic.Renaming

/-! # Two-block CFG calculations for ANF iteration -/

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
variable [InstructionModel Φ τ ε m]

theorem env_ext (Γ : LambdaSSA.VCtx τ) (ρ δ : Env Γ)
    (h : ∀ (i : Nat) {A : τ} (hi : LambdaSSA.At Γ i A),
      Env.get ρ i hi = Env.get δ i hi) : ρ = δ := by
  induction Γ with
  | nil => cases ρ; cases δ; rfl
  | cons B Γ ih =>
      apply Prod.ext
      · apply ih
        intro i A hi
        exact h (i + 1) (by simpa [LambdaSSA.At] using hi)
      · exact h 0 (A := B) (by simp [LambdaSSA.At])

@[simp] theorem envRename_wk (Γ : LambdaSSA.VCtx τ) (B : τ)
    (ρ : Env (B :: Γ)) :
    Env.rename (LambdaSSA.Ren.wk Γ B) ρ = ρ.1 := by
  apply env_ext Γ
  intro i A hi
  rw [Env.rename_get]
  rfl

@[simp] theorem twoLabels_zero (X Z : τ) : twoLabels X Z (0 : Fin 2) = X := rfl

@[simp] theorem twoLabels_one (X Z : τ) : twoLabels X Z (1 : Fin 2) = Z := rfl

@[simp] theorem finCases_two_one {motive : Fin 2 → Sort*}
    (f : motive 0) (g : (i : Fin 1) → motive i.succ) :
    @Fin.cases 1 motive f g (1 : Fin 2) = g (0 : Fin 1) := rfl

theorem ofFn_twoLabels (X Z : τ) : List.ofFn (twoLabels X Z) = [X, Z] := by
  simp [twoLabels, List.ofFn_succ]

@[simp] theorem recursiveInject_two_zero (X Z : τ)
    (h : LambdaSSA.At (List.ofFn (twoLabels X Z)) 0 X) (x : TyDen X) :
    LabelValue.inject 0 h x = Sum.inl x := by
  rfl

@[simp] theorem recursiveInject_two_one (X Z : τ)
    (h : LambdaSSA.At (List.ofFn (twoLabels X Z)) 1 Z) (z : TyDen Z) :
    LabelValue.inject 1 h z = Sum.inr (Sum.inl z) := by
  rfl

/-- Canonical finite decoding of the first block label. -/
@[simp] theorem labelDenToFinite_two_zero (X Z : τ)
    (h : LambdaSSA.At (List.ofFn (twoLabels X Z)) 0 X) (x : TyDen X) :
    labelDenToFinite (twoLabels X Z) (LabelValue.inject 0 h x) =
      finiteLabelInject (twoLabels X Z) 0 x := by
  exact labelDenToFinite_recursiveInject (twoLabels X Z) 0 h x

/-- Canonical finite decoding of the second block label. -/
@[simp] theorem labelDenToFinite_two_one (X Z : τ)
    (h : LambdaSSA.At (List.ofFn (twoLabels X Z)) 1 Z) (z : TyDen Z) :
    labelDenToFinite (twoLabels X Z) (LabelValue.inject 1 h z) =
      finiteLabelInject (twoLabels X Z) 1 z := by
  exact labelDenToFinite_recursiveInject (twoLabels X Z) 1 h z

/-- Both local destinations of the ANF loop CFG route to the recursive side. -/
@[simp] theorem appendSplit_two_inject_zero (L : LambdaSSA.LCtx τ) (X Z : τ)
    (h : LambdaSSA.At (List.ofFn (twoLabels X Z) ++ L) 0 X) (x : TyDen X) :
    LabelValue.appendSplit (List.ofFn (twoLabels X Z)) L
      (LabelValue.inject 0 h x) = Sum.inr (Sum.inl x) := by
  simpa only [ofFn_twoLabels] using
    (LabelValue.appendSplit_inject_local 0 (L := L)
      (by simp [LambdaSSA.At]) h x)

@[simp] theorem appendSplit_two_inject_one (L : LambdaSSA.LCtx τ) (X Z : τ)
    (h : LambdaSSA.At (List.ofFn (twoLabels X Z) ++ L) 1 Z) (z : TyDen Z) :
    LabelValue.appendSplit (List.ofFn (twoLabels X Z)) L
      (LabelValue.inject 1 h z) = Sum.inr (Sum.inr (Sum.inl z)) := by
  simpa only [ofFn_twoLabels] using
    (LabelValue.appendSplit_inject_local 1 (L := L)
      (by simp [LambdaSSA.At]) h z)

/-- An external destination is shifted past both loop blocks. -/
@[simp] theorem appendSplit_two_inject_external
    (L : LambdaSSA.LCtx τ) (X Z : τ) (i : Nat) {A : τ}
    (hL : LambdaSSA.At L i A)
    (h : LambdaSSA.At (List.ofFn (twoLabels X Z) ++ L) (i + 2) A)
    (a : TyDen A) :
    LabelValue.appendSplit (List.ofFn (twoLabels X Z)) L
      (LabelValue.inject (i + 2) h a) =
        Sum.inl (LabelValue.inject i hL a) := by
  simpa only [ofFn_twoLabels] using
    LabelValue.appendSplit_inject_external [X, Z] L i hL h a

/-- Naturality followed by fixpoint exposes the first effectful step of an
iteration while retaining an arbitrary result continuation. -/
theorem iter_naturality
    {X Y A : Type v} (step : X → m (Y ⊕ X)) (k : Y → m A) :
    Isotope.Elgot.kcomp (Isotope.Elgot.iter (m := m) step) k =
      Isotope.Elgot.iter (m := m)
        (Isotope.Elgot.mapReturn (m := m) step k) := by
  exact Isotope.Elgot.LawfulElgotMonad.naturality step k

/-- Inserting a pure administrative state after every effectful loop step
does not change iteration.  This is the exact two-block control shape emitted
for ANF iteration after the result continuation has been absorbed by
`mapReturn`. -/
theorem iter_pure_two_phase {X A : Type v} (g : X → m (A ⊕ X)) :
    Isotope.Elgot.iter (m := m) g =
      fun x => Isotope.Elgot.iter (m := m)
        (fun s : X ⊕ (A ⊕ X) => match s with
          | .inl x => g x >>= fun z => pure (Sum.inr (Sum.inr z))
          | .inr (.inl a) => pure (Sum.inl a)
          | .inr (.inr x) => pure (Sum.inr (Sum.inl x)))
        (Sum.inl x) := by
  let S := X ⊕ (A ⊕ X)
  let q : S → m (A ⊕ S) := fun s => match s with
    | .inl x => g x >>= fun z => pure (Sum.inr (Sum.inr z))
    | .inr (.inl a) => pure (Sum.inl a)
    | .inr (.inr x) => pure (Sum.inr (Sum.inl x))
  let f : S → m ((A ⊕ S) ⊕ S) := fun s => match s with
    | .inl x => g x >>= fun z => pure (Sum.inr (Sum.inr z))
    | .inr (.inl a) => pure (Sum.inl (Sum.inl a))
    | .inr (.inr x) => pure (Sum.inl (Sum.inr (Sum.inl x)))
  have hf : Isotope.Elgot.flattenBody (m := m) f = q := by
    funext s
    cases s with
    | inl x =>
        simp [f, q, Isotope.Elgot.flattenBody, Isotope.Elgot.kcomp,
          Isotope.Elgot.liftPure, Isotope.Elgot.flatten, Function.comp_def,
          LawfulMonad.bind_assoc]
    | inr z => cases z <;> simp [f, q, Isotope.Elgot.flattenBody,
        Isotope.Elgot.kcomp, Isotope.Elgot.liftPure, Isotope.Elgot.flatten,
        Function.comp_def]
  have hstep : Isotope.Elgot.iter (m := m) f ∘ Sum.inl =
      fun x => g x >>= fun z => pure (Sum.map id Sum.inl z) := by
    funext x
    rw [Isotope.Elgot.LawfulElgotMonad.fixpoint]
    simp only [Function.comp_apply, f, LawfulMonad.bind_assoc]
    apply bind_congr
    intro z
    cases z <;> rw [Isotope.Elgot.LawfulElgotMonad.fixpoint] <;>
      simp [f, Function.comp_def]
  have hcomm : Isotope.Elgot.kcomp g
        (Isotope.Elgot.liftPure (m := m) (Sum.map id Sum.inl)) =
      Isotope.Elgot.kcomp (Isotope.Elgot.liftPure (m := m) Sum.inl)
        (Isotope.Elgot.iter (m := m) f) := by
    funext x
    simp only [Isotope.Elgot.kcomp, Isotope.Elgot.liftPure,
      Function.comp_apply, LawfulMonad.bind_pure_comp, LawfulMonad.pure_bind]
    exact congrFun hstep x |>.symm
  have hu := Isotope.Elgot.LawfulElgotMonad.uniformity (m := m)
    g (Isotope.Elgot.iter (m := m) f) Sum.inl hcomm
  rw [hu, Isotope.Elgot.LawfulElgotMonad.codiagonal, hf]
  funext x
  simp [Isotope.Elgot.kcomp, Isotope.Elgot.liftPure, Function.comp_def, q]
  rfl

/-- The form used by the compiled ANF loop: absorb the effectful result
continuation by naturality, then insert the pure dispatcher block. -/
theorem iter_natural_two_phase {X Y A : Type v}
    (step : X → m (Y ⊕ X)) (k : Y → m A) :
    Isotope.Elgot.kcomp (Isotope.Elgot.iter (m := m) step) k =
      fun x => Isotope.Elgot.iter (m := m)
        (fun s : X ⊕ (A ⊕ X) => match s with
          | .inl x => Isotope.Elgot.mapReturn (m := m) step k x >>=
              fun z => pure (Sum.inr (Sum.inr z))
          | .inr (.inl a) => pure (Sum.inl a)
          | .inr (.inr x) => pure (Sum.inr (Sum.inl x)))
        (Sum.inl x) := by
  rw [iter_naturality step k]
  exact iter_pure_two_phase (Isotope.Elgot.mapReturn (m := m) step k)

/-- Split an effectful iteration step and its effectful result continuation
across the two CFG blocks emitted by the compiler. -/
theorem iter_effectful_two_phase {X Y A : Type v}
    (step : X → m (Y ⊕ X)) (k : Y → m A) :
    Isotope.Elgot.kcomp (Isotope.Elgot.iter (m := m) step) k =
      fun x ↦ Isotope.Elgot.iter (m := m)
        (fun s : X ⊕ (Y ⊕ X) ↦ match s with
          | .inl x => step x >>= fun z ↦ pure (Sum.inr (Sum.inr z))
          | .inr (.inl y) => k y >>= fun a ↦ pure (Sum.inl a)
          | .inr (.inr x) => pure (Sum.inr (Sum.inl x)))
        (Sum.inl x) := by
  let g := Isotope.Elgot.mapReturn (m := m) step k
  let S := X ⊕ (Y ⊕ X)
  let q : S → m (A ⊕ S) := fun s ↦ match s with
    | .inl x => step x >>= fun z ↦ pure (Sum.inr (Sum.inr z))
    | .inr (.inl y) => k y >>= fun a ↦ pure (Sum.inl a)
    | .inr (.inr x) => pure (Sum.inr (Sum.inl x))
  let f : S → m ((A ⊕ S) ⊕ S) := fun s ↦ match s with
    | .inl x => step x >>= fun z ↦ pure (Sum.inr (Sum.inr z))
    | .inr (.inl y) => k y >>= fun a ↦ pure (Sum.inl (Sum.inl a))
    | .inr (.inr x) => pure (Sum.inl (Sum.inr (Sum.inl x)))
  have hf : Isotope.Elgot.flattenBody (m := m) f = q := by
    funext s
    cases s with
    | inl x => simp [f, q, Isotope.Elgot.flattenBody, Isotope.Elgot.kcomp,
        Isotope.Elgot.liftPure, Isotope.Elgot.flatten, Function.comp_def,
        LawfulMonad.bind_assoc]
    | inr z => cases z <;> simp [f, q, Isotope.Elgot.flattenBody,
        Isotope.Elgot.kcomp, Isotope.Elgot.liftPure, Isotope.Elgot.flatten,
        Function.comp_def, LawfulMonad.bind_assoc]
  have hstep : Isotope.Elgot.iter (m := m) f ∘ Sum.inl =
      fun x ↦ g x >>= fun z ↦ pure (Sum.map id Sum.inl z) := by
    funext x
    rw [Isotope.Elgot.LawfulElgotMonad.fixpoint]
    simp only [Function.comp_apply, f, g, Isotope.Elgot.mapReturn,
      Isotope.Elgot.kcomp, Isotope.Elgot.liftPure, LawfulMonad.bind_assoc]
    apply bind_congr
    intro z
    cases z with
    | inl y =>
        rw [Isotope.Elgot.LawfulElgotMonad.fixpoint]
        simp [f, Function.comp_def, LawfulMonad.bind_assoc]
    | inr x =>
        rw [Isotope.Elgot.LawfulElgotMonad.fixpoint]
        simp [f, Function.comp_def]
  have hcomm : Isotope.Elgot.kcomp g
        (Isotope.Elgot.liftPure (m := m) (Sum.map id Sum.inl)) =
      Isotope.Elgot.kcomp (Isotope.Elgot.liftPure (m := m) Sum.inl)
        (Isotope.Elgot.iter (m := m) f) := by
    funext x
    simp only [Isotope.Elgot.kcomp, Isotope.Elgot.liftPure,
      Function.comp_apply, LawfulMonad.pure_bind]
    exact congrFun hstep x |>.symm
  have hu := Isotope.Elgot.LawfulElgotMonad.uniformity (m := m)
    g (Isotope.Elgot.iter (m := m) f) Sum.inl hcomm
  rw [iter_naturality step k, hu,
    Isotope.Elgot.LawfulElgotMonad.codiagonal, hf]
  funext x
  simp [Isotope.Elgot.kcomp, Isotope.Elgot.liftPure, Function.comp_def, q]
  rfl

/-- The concrete two-block CFG emitted for an ANF iteration has the same
denotation as source iteration followed by its continuation. -/
theorem let₁_iter_denotes
    {β : LambdaIter.LocallyNameless.BoundCtx τ n}
    {init : Atom Empty Φ n} {loop : Program Empty Φ (n + 1)}
    {body : Program Empty Φ (n + 1)} {X Y A : τ}
    (hinit : Atom.HasType (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty τ) β init X)
    (hloop : Program.HasType (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty τ)
      (β.snoc X) loop (LambdaIter.coprod Y X))
    (hbody : Program.HasType (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty τ)
      (β.snoc Y) body A)
    (sloop : SimpleProgram loop) (sbody : SimpleProgram body)
    {L : LambdaSSA.LCtx τ} {result : Nat} (hout : LambdaSSA.At L result A)
    (dloop : RegionDenotes ε
      (simpleProgram_hasType (L := X :: LambdaIter.coprod Y X :: L) sloop hloop
        (result := 1) (by simp [LambdaSSA.At]))
      (resultEval (ε := ε) (m := m) (L := X :: LambdaIter.coprod Y X :: L)
        (result := 1) hloop (by simp [LambdaSSA.At])))
    (dbody : RegionDenotes ε
      (simpleProgram_hasType (L := X :: LambdaIter.coprod Y X :: L) sbody hbody
        (result := result + 2) (by simpa [LambdaSSA.At] using hout))
      (resultEval (ε := ε) (m := m)
        (L := X :: LambdaIter.coprod Y X :: L) (result := result + 2)
        hbody (by simpa [LambdaSSA.At] using hout))) :
    RegionDenotes ε
      (simpleProgram_hasType (.let₁ (.iter init sloop) sbody)
        (.let₁ (.iter hinit hloop) hbody) hout)
      (resultEval (ε := ε) (m := m) (.let₁ (.iter hinit hloop) hbody) hout) := by
  let Γ := LambdaSSA.LocallyNameless.ToDeBruijn.context β
  let Z := LambdaIter.coprod Y X
  let R := twoLabels X Z
  let finit : Env Γ → m (TyDen X) := fun ρ =>
    LambdaIter.Semantics.denote (ε := ε) (m := m)
      hinit.toLambdaIter PUnit.unit (envToBound ρ)
  let floop : Env (X :: Γ) → m (TyDen Z) := fun ρ =>
    LambdaIter.Semantics.denote (ε := ε) (m := m)
      hloop.toLambdaIter PUnit.unit (envToBound ρ)
  let fbody : Env (Y :: Γ) → m (TyDen A) := fun ρ =>
    LambdaIter.Semantics.denote (ε := ε) (m := m)
      hbody.toLambdaIter PUnit.unit (envToBound ρ)
  have de : RegionDenotes ε
      (LambdaSSA.Region.HasType.br
        (L := List.ofFn R ++ L) (A := X) (ℓ := 0)
        (by simp [R, Z, ofFn_twoLabels, LambdaSSA.At]) (atom_hasType hinit))
      (fun ρ => finit ρ >>= fun x =>
        pure (labelInject (L := List.ofFn R ++ L) 0
          (by simp [R, Z, ofFn_twoLabels, LambdaSSA.At]) x)) := by
    exact RegionDenotes.br (atom_denotes (ε := ε) (m := m) hinit)
  have dloop' : RegionDenotes ε
      (simpleProgram_hasType (L := List.ofFn R ++ L) sloop hloop
        (result := 1) (by simp [R, Z, ofFn_twoLabels, LambdaSSA.At]))
      (fun ρ => floop ρ >>= fun z =>
        pure (labelInject (L := List.ofFn R ++ L) 1
          (by simp [R, Z, ofFn_twoLabels, LambdaSSA.At]) z)) := by
    unfold resultEval at dloop
    simpa only [R, Z, floop, ofFn_twoLabels] using dloop
  have dbody' : RegionDenotes ε
      ((simpleProgram_hasType (L := List.ofFn R ++ L) sbody hbody
        (result := result + 2)
        (by simp [R, Z, ofFn_twoLabels, LambdaSSA.At]; exact hout)).renameVars
          ((LambdaSSA.Ren.wk Γ Z).lift Y))
      (fun ρ : Env (Y :: Z :: Γ) => fbody (ρ.1.1, ρ.2) >>= fun a =>
        pure (labelInject (L := List.ofFn R ++ L) (result + 2)
          (by simp [R, Z, ofFn_twoLabels, LambdaSSA.At]; exact hout) a)) := by
    have d := dbody.renameVars ((LambdaSSA.Ren.wk Γ Z).lift Y)
    have henv (ρ : Env (Y :: Z :: Γ)) :
        Env.rename ((LambdaSSA.Ren.wk Γ Z).lift Y) ρ = (ρ.1.1, ρ.2) := by
      rcases ρ with ⟨⟨γ, z⟩, y⟩
      exact (Env.rename_lift (LambdaSSA.Ren.wk Γ Z) (γ, z) Y y).trans
        (congrArg (fun δ => (δ, y)) (envRename_wk Γ Z (γ, z)))
    unfold resultEval at d
    simpa only [R, Z, fbody, ofFn_twoLabels, henv] using d
  have hlabel0 : LambdaSSA.At (List.ofFn R ++ L) 0 X := by
    simp [R, Z, ofFn_twoLabels, LambdaSSA.At]
  have hvarX : LambdaSSA.At (X :: Z :: Γ) 0 X := by
    simp [LambdaSSA.At]
  have drecur : RegionDenotes ε
      (LambdaSSA.Region.HasType.br
        (Γ := X :: Z :: Γ) (L := List.ofFn R ++ L) (A := X) (ℓ := 0)
        hlabel0 (.var (Φ := Φ) (i := 0) hvarX))
      (fun ρ => (pure (labelInject (L := List.ofFn R ++ L) 0
        hlabel0 ρ.2) :
          m (LabelDen (List.ofFn R ++ L)))) := by
    simpa [Env.get] using
      (RegionDenotes.br (ε := ε) (m := m) (h := hlabel0)
        (Denotes.var (Φ := Φ) (ε := ε) (m := m) hvarX))
  have hvarZ : LambdaSSA.At (Z :: Γ) 0 Z := by simp [LambdaSSA.At]
  have dcase : RegionDenotes ε
      (LambdaSSA.Region.HasType.case
        (Γ := Z :: Γ) (L := List.ofFn R ++ L) (A := Y) (B := X)
        (.var (Φ := Φ) hvarZ)
        ((simpleProgram_hasType (L := List.ofFn R ++ L) sbody hbody
          (result := result + 2)
          (by simp [R, Z, ofFn_twoLabels, LambdaSSA.At]; exact hout)).renameVars
            ((LambdaSSA.Ren.wk Γ Z).lift Y))
        (LambdaSSA.Region.HasType.br
          hlabel0 (.var (Φ := Φ) hvarX)))
      (fun ρ => match TypeModel.coprodEquiv Y X ρ.2 with
        | .inl y => fbody (ρ.1, y) >>= fun a =>
            pure (labelInject (L := List.ofFn R ++ L) (result + 2)
              (by simp [R, Z, ofFn_twoLabels, LambdaSSA.At]; exact hout) a)
        | .inr x => pure (labelInject (L := List.ofFn R ++ L) 0
            hlabel0 x)) := by
    convert RegionDenotes.case
      (Denotes.var (Φ := Φ) (ε := ε) (m := m) hvarZ) dbody' drecur using 1
    funext ρ
    simp only [Env.get, LawfulMonad.pure_bind]
    cases TypeModel.coprodEquiv Y X ρ.2 <;> rfl
  let collective : Env Γ × FiniteLabelDen R →
      m (LabelDen (List.ofFn R ++ L)) := fun p =>
    Fin.cases (fun x => floop (p.1, x) >>= fun z =>
      pure (labelInject (L := List.ofFn R ++ L) 1
        (by simp [R, Z, ofFn_twoLabels, LambdaSSA.At]) z))
      (fun j => Fin.cases (fun z =>
        match TypeModel.coprodEquiv Y X z with
        | .inl y => fbody (p.1, y) >>= fun a =>
            pure (labelInject (L := List.ofFn R ++ L) (result + 2)
              (by simp [R, Z, ofFn_twoLabels, LambdaSSA.At]; exact hout) a)
        | .inr x => pure (labelInject (L := List.ofFn R ++ L) 0
            (by simp [R, Z, ofFn_twoLabels, LambdaSSA.At]) x))
        (fun k => Fin.elim0 k) j) p.2.1 p.2.2
  have dc : CollectiveDenotes Γ R L
      (fun i => Fin.cases (fun ρ => floop ρ >>= fun z =>
          pure (labelInject (L := List.ofFn R ++ L) 1
            (by simp [R, Z, ofFn_twoLabels, LambdaSSA.At]) z))
        (fun j => Fin.cases (fun ρ => match TypeModel.coprodEquiv Y X ρ.2 with
          | .inl y => fbody (ρ.1, y) >>= fun a =>
              pure (labelInject (L := List.ofFn R ++ L) (result + 2)
                (by simp [R, Z, ofFn_twoLabels, LambdaSSA.At]; exact hout) a)
          | .inr x => pure (labelInject (L := List.ofFn R ++ L) 0
              (by simp [R, Z, ofFn_twoLabels, LambdaSSA.At]) x))
          (fun k => Fin.elim0 k) j) i) collective := by
    constructor
    intro i ρ a
    fin_cases i <;> rfl
  simp only [R, Z] at dloop' dcase dc ⊢
  have hentry : LambdaSSA.Region.HasType Γ (.br 0 (atom init))
      (List.ofFn R ++ L) :=
    LambdaSSA.Region.HasType.br hlabel0 (atom_hasType hinit)
  have hblocks : ∀ i, LambdaSSA.Region.HasType (R i :: Γ)
      (Fin.cases (simpleProgram 1 sloop)
        (fun j => Fin.cases
          (.case (.var 0)
            ((simpleProgram (result + 2) sbody).renameVars (LambdaSSA.lift Nat.succ))
            (.br 0 (.var 0)))
          (fun k => nomatch k) j) i)
      (List.ofFn R ++ L) := by
    intro i
    fin_cases i
    · exact simpleProgram_hasType (L := List.ofFn R ++ L) sloop hloop
        (result := 1) (by simp [R, Z, LambdaSSA.At])
    · exact LambdaSSA.Region.HasType.case (.var hvarZ)
        ((simpleProgram_hasType (L := List.ofFn R ++ L) sbody hbody
          (result := result + 2)
          (by simp [R, Z, LambdaSSA.At]; exact hout)).renameVars
            ((LambdaSSA.Ren.wk Γ Z).lift Y))
        (.br hlabel0 (.var hvarX))
  have dcfg := RegionDenotes.cfg (R := R) (collective := collective)
    (entry := .br 0 (atom init))
    (blocks := fun i => Fin.cases (simpleProgram 1 sloop)
      (fun j => Fin.cases
        (.case (.var 0)
          ((simpleProgram (result + 2) sbody).renameVars (LambdaSSA.lift Nat.succ))
          (.br 0 (.var 0)))
        (fun k => nomatch k) j) i)
    hentry hblocks de (fun i => Fin.cases
      (by
        simp only [Fin.cases_zero]
        convert dloop' using 1)
      (fun j => Fin.cases
        (by
          simp only [Fin.cases_succ, Fin.cases_zero]
          convert dcase using 1)
        (fun k => nomatch k) j) i) dc
  convert dcfg using 1
  · rw [simpleProgram]
    congr 1
    funext i
    fin_cases i <;> rfl
  · funext ρ
    unfold resultEval
    simp only [LambdaIter.Semantics.denote, Program.HasType.toLambdaIter,
      Instr.HasType.toLambdaIter, LawfulMonad.bind_assoc]
    let step : TyDen X → m (TyDen Y ⊕ TyDen X) := fun x =>
      floop (ρ, x) >>= fun z => pure (TypeModel.coprodEquiv Y X z)
    let k : TyDen Y → m (LabelDen L) := fun y =>
      fbody (ρ, y) >>= fun a => pure (labelInject result hout a)
    let phase : TyDen X ⊕ (TyDen Y ⊕ TyDen X) →
        m (LabelDen L ⊕ (TyDen X ⊕ (TyDen Y ⊕ TyDen X))) :=
      fun s => match s with
      | .inl x => step x >>= fun z => pure (Sum.inr (Sum.inr z))
      | .inr z => match z with
        | .inl y => k y >>= fun a => pure (Sum.inl a)
        | .inr x => pure (Sum.inr (Sum.inl x))
    have hlocal0 : LambdaSSA.At (List.ofFn R) 0 X := by
      simp [R, Z, ofFn_twoLabels, LambdaSSA.At]
    have hlocal1 : LambdaSSA.At (List.ofFn R) 1 Z := by
      simp [R, Z, ofFn_twoLabels, LambdaSSA.At]
    let enc : TyDen X ⊕ (TyDen Y ⊕ TyDen X) → LabelDen (List.ofFn R) :=
      Sum.elim (LabelValue.inject 0 hlocal0)
        (fun z => LabelValue.inject 1 hlocal1 ((TypeModel.coprodEquiv Y X).symm z))
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
          rw [labelDenToFinite_two_zero X Z hlocal0 x]
          rw [dc.restrict 0 ρ x]
          simp only [Fin.cases_zero]
          simp [step, enc, R, Z, recursiveInject_two_one,
            appendSplit_two_inject_one, labelInject_eq_recursive,
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
              rw [labelDenToFinite_two_one X Z hlocal1
                ((TypeModel.coprodEquiv Y X).symm (Sum.inl y))]
              rw [dc.restrict 1 ρ
                ((TypeModel.coprodEquiv Y X).symm (Sum.inl y))]
              rw [finCases_two_one, Fin.cases_zero]
              simp [R, Z, phase, actual, enc, k, collective, LabelValue.inject,
                Fin.cases, Isotope.Elgot.kcomp,
                Isotope.Elgot.liftPure,
                appendSplit_two_inject_external, LawfulMonad.bind_assoc]
              apply congrArg (fun q => q <$> fbody (ρ, y))
              funext a
              exact (appendSplit_two_inject_external L X Z result hout _ a).symm
          | inr x =>
              dsimp only [phase, enc]
              simp only [phase, enc, Isotope.Elgot.kcomp, Isotope.Elgot.liftPure,
                LawfulMonad.pure_bind, Function.comp_apply, actual]
              change _ = (collective
                (ρ, labelDenToFinite R (LabelValue.inject 1 hlocal1
                  ((TypeModel.coprodEquiv Y X).symm (Sum.inr x)))) >>= fun next =>
                  pure (LabelValue.appendSplit (List.ofFn R) L next))
              rw [labelDenToFinite_two_one X Z hlocal1
                ((TypeModel.coprodEquiv Y X).symm (Sum.inr x))]
              rw [dc.restrict 1 ρ
                ((TypeModel.coprodEquiv Y X).symm (Sum.inr x))]
              rw [finCases_two_one, Fin.cases_zero]
              simp [R, Z, phase, actual, enc, collective, LabelValue.inject,
                Fin.cases, Isotope.Elgot.kcomp,
                Isotope.Elgot.liftPure,
                appendSplit_two_inject_zero]
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
    change (finit ρ >>= fun x =>
      Isotope.Elgot.kcomp (Isotope.Elgot.iter (m := m) step) k x) = _
    rw [iter_effectful_two_phase step k]
    apply bind_congr
    intro x
    rw [LawfulMonad.pure_bind]
    simp only [labelInject_eq_recursive]
    generalize_proofs hentry
    have hr := appendSplit_two_inject_zero L X Z hentry x
    split <;> rename_i hm
    · have hc := hr.symm.trans hm
      contradiction
    · have hc := Sum.inr.inj (hr.symm.trans hm)
      cases hc
      have henc : enc (Sum.inl x) = (Sum.inl x : LabelDen (List.ofFn R)) := by
        dsimp only [enc]
        simpa only [R] using recursiveInject_two_zero X Z hlocal0 x
      have hp := congrFun hphase (Sum.inl x)
      rw [henc] at hp
      simp only [phase, actual, LawfulMonad.bind_pure_comp] at hp ⊢
      convert hp using 1
      apply congrArg (fun q => Isotope.Elgot.iter (m := m) q (Sum.inl x))
      funext s
      cases s with
      | inl x => rfl
      | inr z => cases z <;> rfl

/-- Every simple ANF program is denoted by the SSA region emitted by the
structural compiler. Iteration is discharged by `let₁_iter_denotes`. -/
theorem simpleProgram_denotes
    {β : LambdaIter.LocallyNameless.BoundCtx τ n}
    {p : Program Empty Φ n} (hs : SimpleProgram p)
    (h : Program.HasType (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty τ) β p A)
    {L : LambdaSSA.LCtx τ} {result : Nat} (hout : LambdaSSA.At L result A) :
    RegionDenotes ε (simpleProgram_hasType hs h hout)
      (resultEval (ε := ε) (m := m) h hout) := by
  cases hs with
  | ret a =>
      cases h with
      | ret ha => exact ret_denotes (ε := ε) (m := m) ha hout
  | let₁ hi sb =>
      cases h with
      | let₁ hInstr hBody =>
        cases hi with
        | atom a =>
            cases hInstr with
            | atom ha =>
                exact let₁_atom_denotes (ε := ε) (m := m) ha hBody sb hout
                  (simpleProgram_denotes sb hBody hout)
        | case e sl sr =>
            cases hInstr with
            | case he hl hr =>
                exact let₁_case_denotes (ε := ε) (m := m) he hl hr hBody sl sr sb hout
                  (simpleProgram_denotes sl hl (by simp [LambdaSSA.At]))
                  (simpleProgram_denotes sr hr (by simp [LambdaSSA.At]))
                  (simpleProgram_denotes sb hBody (at_succ hout))
        | iter init sloop =>
            cases hInstr with
            | iter hinit hloop =>
                exact let₁_iter_denotes (ε := ε) (m := m)
                  hinit hloop hBody sloop sb hout
                  (simpleProgram_denotes sloop hloop (by simp [LambdaSSA.At]))
                  (simpleProgram_denotes sb hBody
                    (by simpa [LambdaSSA.At] using hout))
  | let₂ sb =>
      cases h with
      | let₂ ha hBody =>
          exact let₂_denotes (ε := ε) (m := m) ha hBody sb hout
            (simpleProgram_denotes sb hBody hout)
termination_by sizeOf p

/-- Unconditional correctness of the public ANF-to-SSA compiler. -/
theorem program_denotes
    {β : LambdaIter.LocallyNameless.BoundCtx τ n}
    {p : Program Empty Φ n}
    (h : Program.HasType (LambdaIter.Ctx.nil : LambdaIter.Ctx Empty τ) β p A)
    {L : LambdaSSA.LCtx τ} {result : Nat} (hout : LambdaSSA.At L result A) :
    RegionDenotes ε (program_hasType h hout)
      (resultEval (ε := ε) (m := m) h hout) :=
  simpleProgram_denotes (simpleProgram_all p) h hout

end Isotope.LambdaSSA.Translation.ANF.ToSSA
