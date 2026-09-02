import Isotope.LambdaSSA.LocallyNameless.Syntax
import Isotope.LambdaSSA.Syntax

/-! # Closed locally nameless lambda-SSA as de Bruijn lambda-SSA -/

namespace Isotope.LambdaSSA.LocallyNameless.ToDeBruijn

def eraseTm : {n : Nat} → LocallyNameless.Tm Empty Φ n → LambdaSSA.Tm Φ
  | _, .fv x => Empty.elim x
  | _, .bv i => .var i
  | _, .op f a => .op f (eraseTm a)
  | _, .let₁ a b => .let₁ (eraseTm a) (eraseTm b)
  | _, .pair a b => .pair (eraseTm a) (eraseTm b)
  | _, .unit => .unit
  | _, .let₂ a b => .let₂ (eraseTm a) (eraseTm b)
  | _, .inl a => .inl (eraseTm a)
  | _, .inr a => .inr (eraseTm a)
  | _, .case e l r => .case (eraseTm e) (eraseTm l) (eraseTm r)
  | _, .abort a => .abort (eraseTm a)

inductive Tm.Scoped : Nat → LambdaSSA.Tm Φ → Type _ where
  | var (i : Fin n) : Scoped n (.var i)
  | op : Scoped n a → Scoped n (.op f a)
  | let₁ : Scoped n a → Scoped (n + 1) b → Scoped n (.let₁ a b)
  | pair : Scoped n a → Scoped n b → Scoped n (.pair a b)
  | unit : Scoped n .unit
  | let₂ : Scoped n a → Scoped (n + 1 + 1) b → Scoped n (.let₂ a b)
  | inl : Scoped n a → Scoped n (.inl a)
  | inr : Scoped n a → Scoped n (.inr a)
  | case : Scoped n e → Scoped (n + 1) l → Scoped (n + 1) r →
      Scoped n (.case e l r)
  | abort : Scoped n a → Scoped n (.abort a)

def embedTm : {t : LambdaSSA.Tm Φ} → Tm.Scoped n t →
    LocallyNameless.Tm Empty Φ n
  | _, .var i => .bv i
  | _, .op (f := f) h => .op f (embedTm h)
  | _, .let₁ ha hb => .let₁ (embedTm ha) (embedTm hb)
  | _, .pair ha hb => .pair (embedTm ha) (embedTm hb)
  | _, .unit => .unit
  | _, .let₂ ha hb => .let₂ (embedTm ha) (embedTm hb)
  | _, .inl h => .inl (embedTm h)
  | _, .inr h => .inr (embedTm h)
  | _, .case he hl hr => .case (embedTm he) (embedTm hl) (embedTm hr)
  | _, .abort h => .abort (embedTm h)

def scopeTm : (t : LocallyNameless.Tm Empty Φ n) → Tm.Scoped n (eraseTm t)
  | .fv x => Empty.elim x
  | .bv i => .var i
  | .op _ a => .op (scopeTm a)
  | .let₁ a b => .let₁ (scopeTm a) (scopeTm b)
  | .pair a b => .pair (scopeTm a) (scopeTm b)
  | .unit => .unit
  | .let₂ a b => .let₂ (scopeTm a) (scopeTm b)
  | .inl a => .inl (scopeTm a)
  | .inr a => .inr (scopeTm a)
  | .case e l r => .case (scopeTm e) (scopeTm l) (scopeTm r)
  | .abort a => .abort (scopeTm a)

@[simp] theorem eraseTm_embedTm : {t : LambdaSSA.Tm Φ} → (h : Tm.Scoped n t) →
    eraseTm (embedTm h) = t
  | _, .var _ => rfl
  | _, .op h => by simp [embedTm, eraseTm, eraseTm_embedTm h]
  | _, .let₁ ha hb | _, .pair ha hb | _, .let₂ ha hb => by
      simp [embedTm, eraseTm, eraseTm_embedTm ha, eraseTm_embedTm hb]
  | _, .unit => rfl
  | _, .inl h | _, .inr h | _, .abort h => by
      simp [embedTm, eraseTm, eraseTm_embedTm h]
  | _, .case he hl hr => by
      simp [embedTm, eraseTm, eraseTm_embedTm he, eraseTm_embedTm hl, eraseTm_embedTm hr]

@[simp] theorem embedTm_scopeTm : (t : LocallyNameless.Tm Empty Φ n) →
    embedTm (scopeTm t) = t
  | .fv x => Empty.elim x
  | .bv _ | .unit => rfl
  | .op _ a | .inl a | .inr a | .abort a => by simp [embedTm, scopeTm, embedTm_scopeTm a]
  | .let₁ a b | .pair a b | .let₂ a b => by
      simp [embedTm, scopeTm, embedTm_scopeTm a, embedTm_scopeTm b]
  | .case e l r => by
      simp [embedTm, scopeTm, embedTm_scopeTm e, embedTm_scopeTm l, embedTm_scopeTm r]

def eraseRegion : {n l : Nat} → LocallyNameless.Region Empty Empty Φ n l →
    LambdaSSA.Region Φ
  | _, _, .br (.inl i) a => .br i (eraseTm a)
  | _, _, .br (.inr x) _ => Empty.elim x
  | _, _, .case a r s => .case (eraseTm a) (eraseRegion r) (eraseRegion s)
  | _, _, .let₁ a r => .let₁ (eraseTm a) (eraseRegion r)
  | _, _, .let₂ a r => .let₂ (eraseTm a) (eraseRegion r)
  | _, _, .cfg arity entry blocks =>
      .cfg (eraseRegion entry) arity (fun i => eraseRegion (blocks i))

inductive Region.Scoped : Nat → Nat → LambdaSSA.Region Φ → Type _ where
  | br (label : Fin l) : Tm.Scoped n a → Scoped n l (.br label a)
  | case : Tm.Scoped n a → Scoped (n + 1) l r → Scoped (n + 1) l s →
      Scoped n l (.case a r s)
  | let₁ : Tm.Scoped n a → Scoped (n + 1) l r → Scoped n l (.let₁ a r)
  | let₂ : Tm.Scoped n a → Scoped (n + 1 + 1) l r → Scoped n l (.let₂ a r)
  | cfg {arity : Nat} {entry : LambdaSSA.Region Φ}
      {blocks : Fin arity → LambdaSSA.Region Φ} : Scoped n (arity + l) entry →
      (∀ i, Scoped (n + 1) (arity + l) (blocks i)) →
      Scoped n l (.cfg entry arity blocks)

def embedRegion : {r : LambdaSSA.Region Φ} → Region.Scoped n l r →
    LocallyNameless.Region Empty Empty Φ n l
  | _, .br label ha => .br (.inl label) (embedTm ha)
  | _, .case ha hr hs => .case (embedTm ha) (embedRegion hr) (embedRegion hs)
  | _, .let₁ ha hr => .let₁ (embedTm ha) (embedRegion hr)
  | _, .let₂ ha hr => .let₂ (embedTm ha) (embedRegion hr)
  | _, .cfg he hbs => .cfg _ (embedRegion he) (fun i => embedRegion (hbs i))

def scopeRegion : (r : LocallyNameless.Region Empty Empty Φ n l) →
    Region.Scoped n l (eraseRegion r)
  | .br (.inl i) a => .br i (scopeTm a)
  | .br (.inr x) _ => Empty.elim x
  | .case a r s => .case (scopeTm a) (scopeRegion r) (scopeRegion s)
  | .let₁ a r => .let₁ (scopeTm a) (scopeRegion r)
  | .let₂ a r => .let₂ (scopeTm a) (scopeRegion r)
  | .cfg _ entry blocks => .cfg (scopeRegion entry) (fun i => scopeRegion (blocks i))

@[simp] theorem eraseRegion_embedRegion : {r : LambdaSSA.Region Φ} →
    (h : Region.Scoped n l r) → eraseRegion (embedRegion h) = r
  | _, .br _ ha => by simp [embedRegion, eraseRegion, eraseTm_embedTm ha]
  | _, .case ha hr hs => by
      simp [embedRegion, eraseRegion, eraseTm_embedTm ha,
        eraseRegion_embedRegion hr, eraseRegion_embedRegion hs]
  | _, .let₁ ha hr | _, .let₂ ha hr => by
      simp [embedRegion, eraseRegion, eraseTm_embedTm ha, eraseRegion_embedRegion hr]
  | _, .cfg he hbs => by
      simp [embedRegion, eraseRegion, eraseRegion_embedRegion he,
        funext fun i => eraseRegion_embedRegion (hbs i)]

@[simp] theorem embedRegion_scopeRegion :
    (r : LocallyNameless.Region Empty Empty Φ n l) → embedRegion (scopeRegion r) = r
  | .br (.inl _) a => by simp [embedRegion, scopeRegion, embedTm_scopeTm a]
  | .br (.inr x) _ => Empty.elim x
  | .case a r s => by
      simp [embedRegion, scopeRegion, embedTm_scopeTm a,
        embedRegion_scopeRegion r, embedRegion_scopeRegion s]
  | .let₁ a r | .let₂ a r => by
      simp [embedRegion, scopeRegion, embedTm_scopeTm a, embedRegion_scopeRegion r]
  | .cfg _ entry blocks => by
      simp [embedRegion, scopeRegion, embedRegion_scopeRegion entry,
        funext fun i => embedRegion_scopeRegion (blocks i)]

end Isotope.LambdaSSA.LocallyNameless.ToDeBruijn
