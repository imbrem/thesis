import Mathlib.Data.Nat.Notation
import Mathlib.Data.List.OfFn

namespace Isotope

universe ua

inductive SExp (A : Type ua) : Type ua where
  | atom : A → SExp A
  | par: {length : ℕ} → (Fin length → SExp A) → SExp A

namespace SExp

variable {A : Type ua} {A' A'' C}

-- Coercion

instance instCoe : Coe A (SExp A) where
  coe := .atom

-- Lists

def parL (es : List (SExp A)) : SExp A := .par es.get

def nil : SExp A := parL []

instance instEmptyCollection : EmptyCollection (SExp A) where
  emptyCollection := .nil

instance instInhabited : Inhabited (SExp A) where
  default := .nil

theorem nil_def : (∅ : SExp A) = SExp.parL [] := rfl

theorem par_congr {length length'}
  (h : length = length')
  {es : Fin length → SExp A} {es' : Fin length' → SExp A}
  (hes : ∀ i, es i = es' (i.cast h))
  : par es = par es'
  := by cases h; congr; ext i; rw [hes]; rfl

theorem parL_congr {es es' : List (SExp A)}
  (hlength : es.length = es'.length)
  (helem : ∀ i, (_ : i < es.length) -> es[i] = es'[i])
  : parL es = parL es'
  := par_congr (by simp [hlength]) (fun i => helem i i.prop)

theorem parL_ofFn {length} (es : Fin length -> (SExp A)) :
  parL (List.ofFn es) = par es := by
  apply par_congr (by simp)
  intro i
  rw [List.get_eq_getElem, List.getElem_ofFn]
  rfl

theorem par_get (es : List (SExp A)) :
  par es.get = parL es := by simp [parL]

universe ux

inductive ParF (A : Type ua) (X : Type ux) : Type _ where
  | atom (a : A) : ParF A X
  | par {arity : ℕ} (es : Fin arity → X) : ParF A X

@[simp]
def unrollF : SExp A → ParF A (SExp A)
  | .atom a => .atom a
  | .par es => .par es

@[simp]
def ParF.roll : ParF A (SExp A) → SExp A
  | .atom a => .atom a
  | .par es => .par es

@[simp]
theorem ParF.unroll_roll (e : ParF A (SExp A)) :
  e.roll.unrollF = e := by cases e <;> rfl

@[simp]
theorem roll_unrollF (e : SExp A) :
  ParF.roll (unrollF e) = e := by cases e <;> rfl

inductive ParL (A : Type ua) (X : Type ux) : Type _ where
  | atom (a : A) : ParL A X
  | parL (es : List X) : ParL A X

@[simp]
def ParL.roll : ParL A (SExp A) → SExp A
  | .atom a => .atom a
  | .parL es => .parL es

@[simp]
def unrollL : SExp A → ParL A (SExp A)
  | .atom a => .atom a
  | .par es => .parL (List.ofFn es)

@[simp]
theorem ParL.unroll_roll (e : ParL A (SExp A)) :
  e.roll.unrollL = e := by cases e <;> simp [SExp.parL]

@[simp]
theorem roll_unrollL (e : SExp A) :
  ParL.roll (unrollL e) = e := by cases e <;> simp [parL_ofFn, *]

universe ui

def listInduction
  {motive : SExp A → Sort ui}
  (atom : ∀ a, motive (.atom a))
  (parL : ∀ es, (∀ i, (_ : i < es.length) -> motive es[i]) → motive (parL es))
  : ∀ e, motive e
  | .atom a => atom a
  | .par (length := length) es =>
    let hL := parL (List.ofFn es) (fun i h =>
      have h' : i < length := by convert h; simp
      cast (by simp) <| listInduction atom parL (es ⟨i, h'⟩))
    cast (congrArg motive (parL_ofFn _)) hL

-- Equality

instance instDecidableEq [DecidableEq A] : DecidableEq (SExp A)
  | .atom a, .atom b => by simp only [atom.injEq]; apply inferInstance
  | .par (length := n) es, .par (length := n') es' => by
    if h : n = n' then
      cases h
      have hi : ∀ i, Decidable (es i = es' i) := fun i => instDecidableEq (es i) (es' i)
      if h' : ∀ i, es i = es' i then
        apply isTrue; apply par_congr rfl; simp [h']
      else
        apply isFalse;
        simp only [par.injEq, heq_eq_eq, true_and]; intro h; cases h
        simp at h'
    else
      apply isFalse
      simp [*]
  | .atom _, .par _ | .par _, .atom _ => isFalse (by simp)

-- Monad

@[simp]
def mapAtom (f : A → A') : SExp A → SExp A'
  | .atom a => .atom (f a)
  | .par es => .par (fun i => mapAtom f (es i))

@[simp]
theorem mapAtom_id (e : SExp A) :
  mapAtom id e = e := by induction e <;> simp [*]

@[simp]
theorem mapAtom_mapAtom (f : A → A') (g : A' → A'') (e : SExp A) :
  mapAtom g (mapAtom f e) = mapAtom (g ∘ f) e := by induction e <;> simp [*]

@[simp]
def substAtom (f : A → SExp A') : SExp A → SExp A'
  | .atom a => f a
  | .par es => .par (fun i => substAtom f (es i))

@[simp]
theorem substAtom_atom_comp (f : A → A') :
  substAtom (.atom ∘ f) = mapAtom f := by ext e; induction e <;> simp [*]

@[simp]
theorem substAtom_atom (e : SExp A) :
  substAtom .atom e = e := by induction e <;> simp [*]

@[simp]
theorem substAtom_substAtom (f : A → SExp A') (g : A' → SExp A'') (e : SExp A) :
  substAtom g (substAtom f e) = substAtom (fun a => substAtom g (f a)) e := by
  induction e <;> simp [*]

@[simp]
theorem substAtom_parL (f : A → SExp A') (es : List (SExp A)) :
  substAtom f (parL es) = parL (List.map (substAtom f) es) := by
  simp only [parL, substAtom, List.get_eq_getElem]
  apply par_congr (by simp); intro i; simp

@[simp]
theorem mapAtom_parL (f : A → A') (es : List (SExp A)) :
  mapAtom f (parL es) = parL (List.map (mapAtom f) es) := by
  rw [<-substAtom_atom_comp f, substAtom_parL]

@[simp]
theorem mapAtom_nil (f : A → A') :
  mapAtom f ∅ = ∅ := by simp [nil_def]

@[simp]
theorem substAtom_nil (f : A → SExp A') :
  substAtom f ∅ = ∅ := by simp [nil_def]

instance : Monad SExp where
  map f e := e.mapAtom f
  pure a := .atom a
  bind e f := e.substAtom f

theorem map_def (f : A → A') (e : SExp A) :
  f <$> e = mapAtom f e := rfl

@[simp]
theorem map_atom (f : A → A') (a : A) :
  f <$> (SExp.atom a) = .atom (f a) := rfl

@[simp]
theorem map_par (f : A → A') {length} (es : Fin length → SExp A) :
  f <$> (SExp.par es) = .par (fun i => f <$> es i) := rfl

@[simp]
theorem map_parL (f : A → A') (es : List (SExp A)) :
  f <$> (parL es) = parL (mapAtom f <$> es) := by
  rw [map_def, mapAtom_parL]; rfl

theorem bind_def (f : A → SExp A') (e : SExp A) :
  e >>= f = substAtom f e := rfl

@[simp]
theorem bind_atom (f : A → SExp A') (a : A) :
  (SExp.atom a) >>= f = f a := rfl

@[simp]
theorem bind_par (f : A → SExp A') {length} (es : Fin length → SExp A) :
  (SExp.par es) >>= f = .par (es >=> f) := rfl

@[simp]
theorem bind_parL (f : A → SExp A') (es : List (SExp A)) :
  (parL es) >>= f = parL ((fun e => e >>= f) <$> es) := by
  rw [bind_def, substAtom_parL]; rfl

instance : LawfulMonad SExp :=
  LawfulMonad.mk' SExp
    (bind_pure_comp := fun f => congrFun (substAtom_atom_comp f))
    mapAtom_id (fun _ _ => rfl)
    (fun e f g => substAtom_substAtom f g e)

def inlAtom {L R} : SExp L → SExp (L ⊕ R) := mapAtom Sum.inl

def inrAtom {L R} : SExp R → SExp (L ⊕ R) := mapAtom Sum.inr

def cswapAtom {L R} : SExp (L ⊕ R) → SExp (R ⊕ L) := mapAtom Sum.swap

def fstAtom {L R} : SExp (L × R) → SExp L := mapAtom Prod.fst

def sndAtom {L R} : SExp (L × R) → SExp R := mapAtom Prod.snd

def pswapAtom {L R} : SExp (L × R) → SExp (R × L) := mapAtom Prod.swap

def zeroAtom : SExp A → SExp A' := substAtom (fun _ => ∅)

@[simp]
theorem zeroAtom_atom (a : A) :
  zeroAtom (A' := A') (SExp.atom a) = ∅ := rfl

@[simp]
theorem zeroAtom_par {length} (es : Fin length → SExp A) :
  zeroAtom (A' := A') (SExp.par es) = .par (fun i => zeroAtom (es i)) := rfl

@[simp]
theorem zeroAtom_parL (es : List (SExp A)) :
  zeroAtom (A' := A') (parL es) = parL (zeroAtom <$> es) := by
  rw [zeroAtom, substAtom_parL]; rfl

@[simp]
theorem zeroAtom_mapAtom (f : A → A') (e : SExp A) :
  zeroAtom (A' := A'') (mapAtom f e) = zeroAtom e := by induction e <;> simp [*]

@[simp]
theorem mapAtom_zeroAtom (f : A' → A'') (e : SExp A) :
  mapAtom f (zeroAtom (A' := A') e) = zeroAtom e := by induction e <;> simp [*]

@[simp]
theorem zeroAtom_zeroAtom (e : SExp A) :
  zeroAtom (A' := A'') (zeroAtom (A' := A') e) = zeroAtom e
  := by simp [zeroAtom]

def constAtom (c : C) : SExp A → SExp C := mapAtom (fun _ => c)

@[simp]
theorem constAtom_atom (c : C) (x : A) :
  constAtom c (SExp.atom x) = .atom c := rfl

@[simp]
theorem constAtom_par (c : C) {length} (es : Fin length → SExp A) :
  constAtom c (SExp.par es) = .par (fun i => constAtom c (es i)) := rfl

@[simp]
theorem constAtom_parL (c : C) (es : List (SExp A)) :
  constAtom c (parL es) = parL (constAtom c <$> es) := by
  rw [constAtom, mapAtom_parL]; rfl

@[simp]
theorem constAtom_mapAtom (c : C) (f : A → A') (e : SExp A) :
  constAtom c (mapAtom f e) = constAtom c e := by
  rw [constAtom, mapAtom_mapAtom]
  rfl

@[simp]
theorem constAtom_constAtom {A C C'} (c : C) (c' : C') (e : SExp A) :
  constAtom c (constAtom c' e) = constAtom c e := by
  simp only [constAtom, mapAtom_mapAtom]
  rfl

@[simp]
theorem zeroAtom_constAtom (c : C) (e : SExp A) :
  zeroAtom (A' := A') (constAtom c e) = zeroAtom e
  := by rw [constAtom]; simp

@[simp]
theorem constAtom_zeroAtom (c : C) (e : SExp A) :
  constAtom c (zeroAtom (A' := A') e) = zeroAtom e
  := by rw [constAtom]; simp

abbrev eraseAtom : SExp A → SExp Empty := zeroAtom (A' := Empty)

abbrev collapseAtom : SExp A → SExp Unit := constAtom ()

end SExp

end Isotope
