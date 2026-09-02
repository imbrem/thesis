import Isotope.LambdaIter.Named.Alpha
import Isotope.LambdaIter.LocallyNameless.Syntax

/-! # Translation from named to locally nameless lambda-iter terms -/

namespace Isotope.LambdaIter.Named.ToLocallyNameless

/-- The names of the binders currently in scope, newest first. `none` records
an anonymous binder: it occupies an index but cannot resolve a named variable. -/
inductive Scope (ν : Type u) : Nat → Type u where
  | nil : Scope ν 0
  | push (x : Binder ν) (ρ : Scope ν n) : Scope ν (n + 1)

namespace Scope

/-- Resolve a name to the nearest binder carrying it. -/
def lookup [DecidableEq ν] (x : ν) : Scope ν n → Option (Fin n)
  | .nil => none
  | .push none ρ => (ρ.lookup x).map Fin.succ
  | .push (some y) ρ => if x = y then some 0 else (ρ.lookup x).map Fin.succ

/-- Resolve a name as either a bound index or a free name. -/
def resolve [DecidableEq ν] (ρ : Scope ν n) (x : ν) : Fin n ⊕ ν :=
  match ρ.lookup x with
  | some i => .inl i
  | none => .inr x

@[simp] theorem resolve_nil [DecidableEq ν] (x : ν) :
    resolve .nil x = Sum.inr x := rfl

@[simp] theorem resolve_push_none [DecidableEq ν] (ρ : Scope ν n) (x : ν) :
    resolve (.push none ρ) x = (ρ.resolve x).map Fin.succ id := by
  simp [resolve, lookup]
  cases ρ.lookup x <;> rfl

@[simp] theorem resolve_push_self [DecidableEq ν] (ρ : Scope ν n) (x : ν) :
    resolve (.push (some x) ρ) x = Sum.inl 0 := by simp [resolve, lookup]

@[simp] theorem resolve_push_ne [DecidableEq ν] (ρ : Scope ν n) {x y : ν}
    (h : x ≠ y) :
    resolve (.push (some y) ρ) x = (ρ.resolve x).map Fin.succ id := by
  simp [resolve, lookup, h]
  cases ρ.lookup x <;> rfl

/-- Pushing the same binder preserves agreement on a name. -/
theorem resolve_push_eq [DecidableEq ν] {ρ σ : Scope ν n} (q : Binder ν) (x : ν)
    (h : ρ.resolve x = σ.resolve x) :
    (Scope.push q ρ).resolve x = (Scope.push q σ).resolve x := by
  cases q with
  | none => simpa using congrArg (Sum.map Fin.succ id) h
  | some y =>
      by_cases e : x = y
      · subst e; simp
      · simpa [resolve_push_ne _ e] using congrArg (Sum.map Fin.succ id) h

/-- Extending two related substitution environments by a binder which is
neither the substituted name nor the fresh replacement preserves the relation. -/
theorem resolve_push_rename [DecidableEq ν] {ρ σ : Scope ν n}
    {x y z : ν} {q : Binder ν} (hqx : q ≠ some x) (hqy : q ≠ some y)
    (h : ρ.resolve z = σ.resolve (if x = z then y else z)) :
    (Scope.push q ρ).resolve z =
      (Scope.push q σ).resolve (if x = z then y else z) := by
  cases q with
  | none => simpa using congrArg (Sum.map Fin.succ id) h
  | some w =>
      simp only [Option.some.injEq, ne_eq] at hqx hqy
      by_cases e : x = z
      · subst z
        have h' : ρ.resolve x = σ.resolve y := by simpa using h
        rw [if_pos rfl]
        rw [resolve_push_ne _ (fun e => hqx e.symm)]
        rw [resolve_push_ne _ (fun e => hqy e.symm)]
        exact congrArg (Sum.map Fin.succ id) h'
      · by_cases ew : z = w
        · subst z; simp [e]
        · simp [resolve_push_ne, ew, e, h]

/-- Once a binder shadows `x`, differences in the environments' resolutions
of `x` are irrelevant. -/
theorem resolve_push_shadow [DecidableEq ν] {ρ σ : Scope ν n} {x z : ν}
    (h : z ≠ x → ρ.resolve z = σ.resolve z) :
    (Scope.push (some x) ρ).resolve z = (Scope.push (some x) σ).resolve z := by
  by_cases e : z = x
  · subst z; simp
  · simpa [resolve_push_ne _ e] using congrArg (Sum.map Fin.succ id) (h e)

end Scope

/-- Translate a named term relative to its enclosing named binders. -/
def translate [DecidableEq ν] (ρ : Scope ν n) :
    Named.Tm ν Φ → LocallyNameless.Tm ν Φ n
  | .var x => match ρ.resolve x with
    | .inl i => .bv i
    | .inr x => .fv x
  | .op f a => .op f (translate ρ a)
  | .let₁ x a b => .let₁ (translate ρ a) (translate (.push x ρ) b)
  | .unit => .unit
  | .pair a b => .pair (translate ρ a) (translate ρ b)
  | .let₂ x y a b => .let₂ (translate ρ a) (translate (.push y (.push x ρ)) b)
  | .inl a => .inl (translate ρ a)
  | .inr a => .inr (translate ρ a)
  | .case e x a y b =>
      .case (translate ρ e) (translate (.push x ρ) a) (translate (.push y ρ) b)
  | .abort a => .abort (translate ρ a)
  | .iter a x b => .iter (translate ρ a) (translate (.push x ρ) b)

/-- Translation depends only on the resolution of names free in the term. -/
theorem translate_congr [DecidableEq ν] {ρ σ : Scope ν n} (a : Named.Tm ν Φ)
    (h : ∀ x, a.Free x → ρ.resolve x = σ.resolve x) :
    translate ρ a = translate σ a := by
  induction a generalizing n with
  | var x =>
      simp only [Tm.Free] at h
      rw [translate, translate, h x rfl]
  | op f a ih =>
      simp only [translate]
      rw [ih fun x hx => h x hx]
  | let₁ q a b iha ihb =>
      simp only [translate]
      rw [iha fun x hx => h x (Or.inl hx)]
      rw [ihb]
      intro x hx
      by_cases e : q = some x
      · rw [e]; simp
      · exact Scope.resolve_push_eq q x (h x (Or.inr ⟨e, hx⟩))
  | unit => rfl
  | pair a b iha ihb =>
      simp only [translate]
      rw [iha fun x hx => h x (Or.inl hx), ihb fun x hx => h x (Or.inr hx)]
  | let₂ q r a b iha ihb =>
      simp only [translate]
      rw [iha fun x hx => h x (Or.inl hx)]
      rw [ihb]
      intro x hx
      by_cases er : r = some x
      · rw [er]; simp
      · apply Scope.resolve_push_eq
        by_cases eq : q = some x
        · rw [eq]; simp
        · exact Scope.resolve_push_eq q x (h x (Or.inr ⟨eq, er, hx⟩))
  | inl a ih | inr a ih | abort a ih =>
      simp only [translate]
      rw [ih fun x hx => h x hx]
  | case e q a r b ihe iha ihb =>
      simp only [translate]
      rw [ihe fun x hx => h x (Or.inl hx)]
      rw [iha]
      · rw [ihb]
        intro x hx
        by_cases er : r = some x
        · rw [er]; simp
        · exact Scope.resolve_push_eq r x (h x (Or.inr (Or.inr ⟨er, hx⟩)))
      · intro x hx
        by_cases eq : q = some x
        · rw [eq]; simp
        · exact Scope.resolve_push_eq q x (h x (Or.inr (Or.inl ⟨eq, hx⟩)))
  | iter a q b iha ihb =>
      simp only [translate]
      rw [iha fun x hx => h x (Or.inl hx)]
      rw [ihb]
      intro x hx
      by_cases eq : q = some x
      · rw [eq]; simp
      · exact Scope.resolve_push_eq q x (h x (Or.inr ⟨eq, hx⟩))

def translateClosed [DecidableEq ν] (a : Named.Tm ν Φ) :
    LocallyNameless.Tm ν Φ 0 := translate .nil a

/-- Two named terms have the same locally nameless image in every enclosing
scope. Quantifying over scopes makes this relation compositional under binders. -/
def SameLocallyNameless [DecidableEq ν] (a b : Named.Tm ν Φ) : Prop :=
  ∀ {n} (ρ : Scope ν n), translate ρ a = translate ρ b

namespace SameLocallyNameless

variable [DecidableEq ν] {a b c : Named.Tm ν Φ}

@[refl] theorem refl (a : Named.Tm ν Φ) : SameLocallyNameless a a := fun _ => rfl
@[symm] theorem symm (h : SameLocallyNameless a b) : SameLocallyNameless b a :=
  fun ρ => (h ρ).symm
@[trans] theorem trans (h₁ : SameLocallyNameless a b)
    (h₂ : SameLocallyNameless b c) : SameLocallyNameless a c :=
  fun ρ => (h₁ ρ).trans (h₂ ρ)

theorem op (h : SameLocallyNameless a b) :
    SameLocallyNameless (.op f a) (.op f b) :=
  fun ρ => congrArg (LocallyNameless.Tm.op f) (h ρ)
theorem let₁ (ha : SameLocallyNameless a a') (hb : SameLocallyNameless b b') :
    SameLocallyNameless (.let₁ x a b) (.let₁ x a' b') :=
  fun ρ => by simp only [translate, ha ρ, hb (.push x ρ)]
theorem pair (ha : SameLocallyNameless a a') (hb : SameLocallyNameless b b') :
    SameLocallyNameless (.pair a b) (.pair a' b') :=
  fun ρ => by simp only [translate, ha ρ, hb ρ]
theorem let₂ (ha : SameLocallyNameless a a') (hb : SameLocallyNameless b b') :
    SameLocallyNameless (.let₂ x y a b) (.let₂ x y a' b') :=
  fun ρ => by simp only [translate, ha ρ, hb (.push y (.push x ρ))]
theorem inl (h : SameLocallyNameless a b) :
    SameLocallyNameless (.inl a) (.inl b) :=
  fun ρ => congrArg
    (fun t : LocallyNameless.Tm ν Φ _ => LocallyNameless.Tm.inl t) (h ρ)
theorem inr (h : SameLocallyNameless a b) :
    SameLocallyNameless (.inr a) (.inr b) :=
  fun ρ => congrArg
    (fun t : LocallyNameless.Tm ν Φ _ => LocallyNameless.Tm.inr t) (h ρ)
theorem case {e e' l l' r r' : Named.Tm ν Φ}
    (he : SameLocallyNameless e e')
    (hl : SameLocallyNameless l l') (hr : SameLocallyNameless r r') :
    SameLocallyNameless (.case e x l y r) (.case e' x l' y r') :=
  fun ρ => by simp only [translate, he ρ, hl (.push x ρ), hr (.push y ρ)]
theorem abort (h : SameLocallyNameless a b) :
    SameLocallyNameless (.abort a) (.abort b) :=
  fun ρ => congrArg
    (fun t : LocallyNameless.Tm ν Φ _ => LocallyNameless.Tm.abort t) (h ρ)
theorem iter (ha : SameLocallyNameless a a') (hb : SameLocallyNameless b b') :
    SameLocallyNameless (.iter a x b) (.iter a' x b') :=
  fun ρ => by simp only [translate, ha ρ, hb (.push x ρ)]

theorem translateClosed_eq (h : SameLocallyNameless a b) :
    translateClosed a = translateClosed b := h .nil

end SameLocallyNameless

@[simp] theorem translateClosed_var [DecidableEq ν] (x : ν) :
    translateClosed (Φ := Φ) (.var x) = .fv x := rfl

@[simp] theorem translate_var_bound [DecidableEq ν] (x : ν) (ρ : Scope ν n) :
    translate (.push (some x) ρ) (Named.Tm.var x : Named.Tm ν Φ) = .bv 0 := by
  simp [translate]

@[simp] theorem translate_var_under_anonymous [DecidableEq ν]
    (x : ν) (ρ : Scope ν n) :
    translate (.push none ρ) (Named.Tm.var x : Named.Tm ν Φ) =
      (translate ρ (.var x)).lift := by
  simp only [translate, Scope.resolve_push_none, LocallyNameless.Tm.lift]
  cases ρ.resolve x <;> rfl

end Isotope.LambdaIter.Named.ToLocallyNameless
