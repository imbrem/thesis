import Isotope.LambdaIter.NoSubtyping.Metatheory

/-! Algebra of locally nameless renaming and substitution. -/

namespace Isotope.LambdaIter.NoSubtyping.LocallyNameless

open Isotope.LambdaIter.LocallyNameless
open Isotope.LambdaIter.LocallyNameless.Tm

namespace Syntax

/-- Lift a renaming through one binder. -/
def upRen (ρ : Fin n → Fin m) : Fin (n + 1) → Fin (m + 1) :=
  Fin.cases 0 (fun i => Fin.succ (ρ i))

/-- Lift a simultaneous substitution through one binder. -/
def upSub (σ : Fin n → Tm ν Φ m) : Fin (n + 1) → Tm ν Φ (m + 1) :=
  Fin.cases (.bv 0) (fun i => (σ i).lift)

@[simp] theorem upRen_zero (ρ : Fin n → Fin m) : upRen ρ 0 = 0 := rfl
@[simp] theorem upRen_succ (ρ : Fin n → Fin m) (i : Fin n) :
    upRen ρ i.succ = (ρ i).succ := rfl
@[simp] theorem upSub_zero (σ : Fin n → Tm ν Φ m) : upSub σ 0 = .bv 0 := rfl
@[simp] theorem upSub_succ (σ : Fin n → Tm ν Φ m) (i : Fin n) :
    upSub σ i.succ = (σ i).lift := rfl

@[simp] theorem rename_fv (ρ : Fin n → Fin m) :
    rename ρ (.fv x : Tm ν Φ n) = .fv x := rfl
@[simp] theorem rename_bv (ρ : Fin n → Fin m) (i : Fin n) :
    rename ρ (.bv i : Tm ν Φ n) = .bv (ρ i) := rfl
@[simp] theorem rename_op (ρ : Fin n → Fin m) :
    rename ρ (.op f a) = .op f (rename ρ a) := rfl
@[simp] theorem rename_let₁ (ρ : Fin n → Fin m) :
    rename ρ (.let₁ a b) = .let₁ (rename ρ a) (rename (upRen ρ) b) := rfl
@[simp] theorem rename_unit (ρ : Fin n → Fin m) :
    rename ρ (.unit : Tm ν Φ n) = .unit := rfl
@[simp] theorem rename_pair (ρ : Fin n → Fin m) :
    rename ρ (.pair a b) = .pair (rename ρ a) (rename ρ b) := rfl
@[simp] theorem rename_let₂ (ρ : Fin n → Fin m) :
    rename ρ (.let₂ a b) = .let₂ (rename ρ a) (rename (upRen (upRen ρ)) b) := rfl
@[simp] theorem rename_inl (ρ : Fin n → Fin m) :
    rename ρ (.inl a) = .inl (rename ρ a) := rfl
@[simp] theorem rename_inr (ρ : Fin n → Fin m) :
    rename ρ (.inr a) = .inr (rename ρ a) := rfl
@[simp] theorem rename_case (ρ : Fin n → Fin m) :
    rename ρ (.case e l r) =
      .case (rename ρ e) (rename (upRen ρ) l) (rename (upRen ρ) r) := rfl
@[simp] theorem rename_abort (ρ : Fin n → Fin m) :
    rename ρ (.abort a) = .abort (rename ρ a) := rfl
@[simp] theorem rename_iter (ρ : Fin n → Fin m) :
    rename ρ (.iter a b) = .iter (rename ρ a) (rename (upRen ρ) b) := rfl

@[simp] theorem bsubst_fv (σ : Fin n → Tm ν Φ m) :
    bsubst σ (.fv x : Tm ν Φ n) = .fv x := rfl
@[simp] theorem bsubst_bv (σ : Fin n → Tm ν Φ m) (i : Fin n) :
    bsubst σ (.bv i : Tm ν Φ n) = σ i := rfl
@[simp] theorem bsubst_op (σ : Fin n → Tm ν Φ m) :
    bsubst σ (.op f a) = .op f (bsubst σ a) := rfl
@[simp] theorem bsubst_let₁ (σ : Fin n → Tm ν Φ m) :
    bsubst σ (.let₁ a b) = .let₁ (bsubst σ a) (bsubst (upSub σ) b) := rfl
@[simp] theorem bsubst_unit (σ : Fin n → Tm ν Φ m) :
    bsubst σ (.unit : Tm ν Φ n) = .unit := rfl
@[simp] theorem bsubst_pair (σ : Fin n → Tm ν Φ m) :
    bsubst σ (.pair a b) = .pair (bsubst σ a) (bsubst σ b) := rfl
@[simp] theorem bsubst_let₂ (σ : Fin n → Tm ν Φ m) :
    bsubst σ (.let₂ a b) = .let₂ (bsubst σ a) (bsubst (upSub (upSub σ)) b) := rfl
@[simp] theorem bsubst_inl (σ : Fin n → Tm ν Φ m) :
    bsubst σ (.inl a) = .inl (bsubst σ a) := rfl
@[simp] theorem bsubst_inr (σ : Fin n → Tm ν Φ m) :
    bsubst σ (.inr a) = .inr (bsubst σ a) := rfl
@[simp] theorem bsubst_case (σ : Fin n → Tm ν Φ m) :
    bsubst σ (.case e l r) =
      .case (bsubst σ e) (bsubst (upSub σ) l) (bsubst (upSub σ) r) := rfl
@[simp] theorem bsubst_abort (σ : Fin n → Tm ν Φ m) :
    bsubst σ (.abort a) = .abort (bsubst σ a) := rfl
@[simp] theorem bsubst_iter (σ : Fin n → Tm ν Φ m) :
    bsubst σ (.iter a b) = .iter (bsubst σ a) (bsubst (upSub σ) b) := rfl

theorem rename_congr {ρ ρ' : Fin n → Fin m} (h : ∀ i, ρ i = ρ' i) (t : Tm ν Φ n) :
    rename ρ t = rename ρ' t := by
  apply congrArg (fun f => rename f t)
  funext i
  exact h i

theorem bsubst_congr {σ σ' : Fin n → Tm ν Φ m} (h : ∀ i, σ i = σ' i)
    (t : Tm ν Φ n) : bsubst σ t = bsubst σ' t := by
  apply congrArg (fun f => bsubst f t)
  funext i
  exact h i

@[simp] theorem upRen_id : upRen (fun i : Fin n => i) = fun i => i := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

theorem upRen_comp (ρ : Fin n → Fin m) (ρ' : Fin m → Fin k) :
    upRen (fun i => ρ' (ρ i)) = fun i => upRen ρ' (upRen ρ i) := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

@[simp] theorem rename_id (t : Tm ν Φ n) : rename (fun i => i) t = t := by
  induction t with
  | fv | bv | unit => rfl
  | op _ _ ih | inl _ ih | inr _ ih | abort _ ih => simp [ih]
  | let₁ _ _ iha ihb =>
      simp only [rename_let₁, iha]
      rw [upRen_id, ihb]
  | pair _ _ iha ihb => simp [iha, ihb]
  | let₂ _ _ iha ihb =>
      simp only [rename_let₂, iha]
      rw [upRen_id, upRen_id, ihb]
  | case _ _ _ ihe ihl ihr =>
      simp only [rename_case, ihe]
      rw [upRen_id, ihl, ihr]
  | iter _ _ iha ihb =>
      simp only [rename_iter, iha]
      rw [upRen_id, ihb]

theorem rename_comp (ρ : Fin n → Fin m) (ρ' : Fin m → Fin k) (t : Tm ν Φ n) :
    rename ρ' (rename ρ t) = rename (fun i => ρ' (ρ i)) t := by
  induction t generalizing m k with
  | fv | bv | unit => rfl
  | op _ _ ih | inl _ ih | inr _ ih | abort _ ih => simp [ih]
  | let₁ _ _ iha ihb =>
      simp [iha, ihb, ← upRen_comp]
  | pair _ _ iha ihb => simp [iha, ihb]
  | let₂ _ _ iha ihb => simp [iha, ihb, ← upRen_comp]
  | case _ _ _ ihe ihl ihr => simp [ihe, ihl, ihr, ← upRen_comp]
  | iter _ _ iha ihb => simp [iha, ihb, ← upRen_comp]

@[simp] theorem rename_lift (ρ : Fin n → Fin m) (t : Tm ν Φ n) :
    rename (upRen ρ) t.lift = (rename ρ t).lift := by
  rw [lift, rename_comp, lift, rename_comp]
  apply rename_congr
  intro i
  rfl

@[simp] theorem rename_underBinder (ρ : Fin n → Fin m) (t : Tm ν Φ (n + 1)) :
    rename (upRen (upRen ρ)) t.underBinder = (rename (upRen ρ) t).underBinder := by
  rw [underBinder, rename_comp, underBinder, rename_comp]
  apply rename_congr
  intro i
  exact Fin.cases rfl (fun _ => rfl) i

@[simp] theorem rename_underTwoBinders (ρ : Fin n → Fin m) (t : Tm ν Φ (n + 2)) :
    rename (upRen (upRen (upRen ρ))) t.underTwoBinders =
      (rename (upRen (upRen ρ)) t).underTwoBinders := by
  rw [underTwoBinders, rename_comp, underTwoBinders, rename_comp]
  apply rename_congr
  intro i
  exact Fin.cases rfl (Fin.cases rfl (fun _ => rfl)) i

private theorem rename_upSub (ρ : Fin m → Fin k) (σ : Fin n → Tm ν Φ m) :
    (fun i => rename (upRen ρ) (upSub σ i)) = upSub (fun i => rename ρ (σ i)) := by
  funext i
  refine Fin.cases rfl (fun j => ?_) i
  exact rename_lift ρ (σ j)

/-- Renaming after simultaneous substitution acts pointwise on the images. -/
theorem rename_bsubst (ρ : Fin m → Fin k) (σ : Fin n → Tm ν Φ m)
    (t : Tm ν Φ n) :
    rename ρ (bsubst σ t) = bsubst (fun i => rename ρ (σ i)) t := by
  induction t generalizing m k with
  | fv | bv | unit => rfl
  | op _ _ ih | inl _ ih | inr _ ih | abort _ ih => simp [ih]
  | let₁ _ _ iha ihb =>
      simp only [bsubst_let₁, rename_let₁, iha]
      rw [ihb]
      congr 1
      exact bsubst_congr (congrFun (rename_upSub ρ σ)) _
  | pair _ _ iha ihb => simp [iha, ihb]
  | let₂ _ _ iha ihb =>
      simp only [bsubst_let₂, rename_let₂, iha]
      rw [ihb]
      congr 1
      apply bsubst_congr
      exact congrFun ((rename_upSub (upRen ρ) (upSub σ)).trans
        (congrArg (fun f => upSub f) (rename_upSub ρ σ)))
  | case _ _ _ ihe ihl ihr =>
      simp only [bsubst_case, rename_case, ihe]
      rw [ihl, ihr]
      congr 1 <;> apply bsubst_congr <;> exact congrFun (rename_upSub ρ σ)
  | iter _ _ iha ihb =>
      simp only [bsubst_iter, rename_iter, iha]
      rw [ihb]
      congr 1
      exact bsubst_congr (congrFun (rename_upSub ρ σ)) _

private theorem upSub_comp_ren (σ : Fin m → Tm ν Φ k) (ρ : Fin n → Fin m) :
    (fun i => upSub σ (upRen ρ i)) = upSub (fun i => σ (ρ i)) := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

/-- Simultaneous substitution after renaming composes the index map into the
substitution. -/
theorem bsubst_rename (σ : Fin m → Tm ν Φ k) (ρ : Fin n → Fin m)
    (t : Tm ν Φ n) :
    bsubst σ (rename ρ t) = bsubst (fun i => σ (ρ i)) t := by
  induction t generalizing m k with
  | fv | bv | unit => rfl
  | op _ _ ih | inl _ ih | inr _ ih | abort _ ih => simp [ih]
  | let₁ _ _ iha ihb =>
      simp only [rename_let₁, bsubst_let₁, iha]
      rw [ihb]
      congr 1
      exact bsubst_congr (congrFun (upSub_comp_ren σ ρ)) _
  | pair _ _ iha ihb => simp [iha, ihb]
  | let₂ _ _ iha ihb =>
      simp only [rename_let₂, bsubst_let₂, iha]
      rw [ihb]
      congr 1
      apply bsubst_congr
      exact congrFun ((upSub_comp_ren (upSub σ) (upRen ρ)).trans
        (congrArg (fun f => upSub f) (upSub_comp_ren σ ρ)))
  | case _ _ _ ihe ihl ihr =>
      simp only [rename_case, bsubst_case, ihe]
      rw [ihl, ihr]
      congr 1 <;> apply bsubst_congr <;> exact congrFun (upSub_comp_ren σ ρ)
  | iter _ _ iha ihb =>
      simp only [rename_iter, bsubst_iter, iha]
      rw [ihb]
      congr 1
      exact bsubst_congr (congrFun (upSub_comp_ren σ ρ)) _

@[simp] theorem rename_instantiate (ρ : Fin n → Fin m) (b : Tm ν Φ (n + 1))
    (a : Tm ν Φ n) :
    rename ρ (instantiate b a) = instantiate (rename (upRen ρ) b) (rename ρ a) := by
  rw [instantiate, rename_bsubst, instantiate]
  rw [bsubst_rename]
  apply bsubst_congr
  intro i
  refine Fin.cases rfl (fun _ => rfl) i

end Syntax
end Isotope.LambdaIter.NoSubtyping.LocallyNameless
