import Isotope.STm.Defs

namespace Isotope

open Args

namespace STm

variable {Arity} [instArgs : Args Arity] {L : STm.Lang Arity}

variable {A A₁ A₂ A₃}

def Closed (L : STm.Lang Arity) := STm L Empty

inductive Mem (a : A) : STm L A → Prop where
  | sym : Mem a (.sym a)
  | op {arity} {o : L.Op arity} {es : Ix arity → STm L A} :
    (i : Ix arity) → (Mem a (es i)) → Mem a (.op o es)

inductive UseOf (a : A) : STm L A → Type where
  | sym : UseOf a (.sym a)
  | op {arity} {o : L.Op arity} {es : Ix arity → STm L A} :
    (i : Ix arity) → (UseOf a (es i)) → UseOf a (.op o es)

inductive Use : STm L A → Type where
  | sym (a) : Use (.sym a : STm L A)
  | op {arity} {o : L.Op arity} {es : Ix arity → STm L A} :
    (i : Ix arity) → (Use (es i)) → Use (.op o es)

variable {a : A} {e : STm L A}

instance instMembership : Membership A (STm L A) where
  mem e a := Mem a e

inductive IsClosed : STm L A → Prop where
  | const {c} : IsClosed (.const c)
  | op {arity} {o : L.Op arity} {es : Ix arity → STm L A} :
    (∀ i : Ix arity, IsClosed (es i)) → IsClosed (.op o es)

attribute [simp] IsClosed.const

inductive IsOpen : STm L A → Prop where
  | sym {a} : IsOpen (.sym a)
  | op {arity} {o : L.Op arity} {es : Ix arity → STm L A} :
    (i : Ix arity) → IsOpen (es i) → IsOpen (.op o es)

attribute [simp] IsOpen.sym

theorem Mem.open (h : a ∈ e) : IsOpen e
  := by induction h <;> constructor <;> assumption

theorem mem_sym : a ∈ (.sym a : STm L A) := Mem.sym

@[simp]
theorem mem_sym_iff {a b : A} : a ∈ (.sym b : STm L A) ↔ a = b
  := ⟨fun | .sym => rfl, fun | rfl => .sym⟩

@[simp]
theorem mem_op_iff {arity} {o : L.Op arity} {es : Ix arity → STm L A} :
  a ∈ (.op o es : STm L A) ↔ ∃ i, a ∈ es i
  := ⟨fun | .op i h => ⟨i, h⟩, fun ⟨i, h⟩ => .op i h⟩

@[simp]
theorem Mem.not_const {c} : a ∉ (.const c : STm L A)
  := fun h => nomatch h

theorem not_mem_sym_iff {a b : A} : a ∉ (.sym b : STm L A) ↔ a ≠ b
  := by simp

theorem not_mem_op_iff {arity} {o : L.Op arity} {es : Ix arity → STm L A} :
  a ∉ (.op o es : STm L A) ↔ ∀ i, a ∉ es i
  := by simp

theorem IsClosed.arg
  {arity} {o : L.Op arity} {es : Ix arity → STm L A} (i) :
  IsClosed (.op o es) → IsClosed (es i)
  | .op h => h i

@[simp]
theorem IsClosed.op_iff {arity} {o : L.Op arity} {es : Ix arity → STm L A} :
  IsClosed (.op o es) ↔ ∀ i, IsClosed (es i)
  := ⟨fun | .op h => h, fun h => .op h⟩

@[simp]
theorem IsClosed.not_sym : ¬ IsClosed (.sym a : STm L A)
  := fun h => nomatch h

theorem IsClosed.not_mem (h : IsClosed e) : a ∉ e
  := by induction h <;> simp [*]

theorem Mem.not_closed (h : a ∈ e) : ¬ IsClosed e
  := fun hc => hc.not_mem h

theorem IsClosed.of_not_mem (h : ∀ a, a ∉ e) : IsClosed e
  := by induction e <;> simp at *; simp [*]

theorem IsClosed.not_mem_iff : IsClosed e ↔ ∀ a, a ∉ e
  := ⟨fun h _ => h.not_mem, of_not_mem⟩

theorem IsOpen.not_const : ¬ IsOpen (.const c : STm L A)
  := fun h => nomatch h

theorem IsOpen.op_iff {arity} {o : L.Op arity} {es : Ix arity → STm L A} :
  IsOpen (.op o es) ↔ ∃ i, IsOpen (es i)
  := ⟨fun | .op i h => ⟨i, h⟩, fun ⟨i, h⟩ => .op i h⟩

@[simp]
theorem UseOf.mem (u : UseOf a e) : a ∈ e
  := by induction u <;> constructor <;> assumption

@[simp]
theorem UseOf.open (u : UseOf a e) : IsOpen e
  := u.mem.open

@[simp]
theorem UseOf.not_closed (u : UseOf a e) : ¬ IsClosed e
  := u.mem.not_closed

@[simp]
def UseOf.atom (_ : UseOf a e) : A := a

@[simp]
def UseOf.tm (_ : UseOf a e) : STm L A := e

@[simp]
def UseOf.ix {arity} {o : L.Op arity}
  {es : Ix arity → STm L A}
  : UseOf a (.op o es) -> Ix arity
  | .op i _ => i

@[simp]
def UseOf.arg {arity}
  {o : L.Op arity}
  {es : Ix arity → STm L A}
  : (u : UseOf a (.op o es)) -> UseOf a (es (u.ix))
  | .op _ h => h

@[simp]
def UseOf.depth {a : A} {e : STm L A} : UseOf a e → ℕ
  | .sym => 0
  | .op _ h => h.depth + 1

@[simp]
def Use.atom {e : STm L A} : Use e → A
  | .sym a => a
  | .op _ h => h.atom

@[simp]
def Use.tm (_ : Use e) : STm L A := e

@[simp]
def Use.arity
  {arity} {o : L.Op arity} {es : Ix arity → STm L A} (_ : Use (.op o es)) : Arity
  := arity

@[simp]
def Use.ix {arity} {o : L.Op arity}
  {es : Ix arity → STm L A}
  : Use (.op o es) -> Ix arity
  | .op i _ => i

@[simp]
def Use.arg {arity}
  {o : L.Op arity}
  {es : Ix arity → STm L A}
  : (u : Use (.op o es)) -> Use (es (u.ix))
  | .op _ h => h

def UseOf.use {a : A} {e : STm L A} : UseOf a e → Use e
  | .sym => .sym a
  | .op i h => .op i h.use

def Use.useOf {e : STm L A} : (u : Use e) → UseOf u.atom e
  | .sym a => .sym
  | .op i h => .op i h.useOf

def UseOf.cast {a a' : A} {e' e : STm L A}
  (ha : a = a')
  (u : UseOf a e)
  (he : e = e') : UseOf a' e'
  := by cases ha; cases he; exact u

@[simp]
theorem UseOf.cast_refl (u : UseOf a e) : u.cast rfl rfl = u := rfl

@[simp]
theorem UseOf.cast_cast {a a' a'' : A} {e e' e'' : STm L A}
  (ha₁ : a = a') (ha₂ : a' = a'')
  (u : UseOf a e)
  (he₁ : e = e') (he₂ : e' = e'') :
  (u.cast ha₁ he₁).cast ha₂ he₂
  = u.cast (ha₁.trans ha₂) (he₁.trans he₂)
  := by cases ha₁; cases ha₂; cases he₁; cases he₂; rfl

def Use.cast {e e' : STm L A} (he : e = e') (u : Use e) : Use e'
  := by cases he; exact u

@[simp]
theorem Use.cast_refl (u : Use e) : u.cast rfl = u := rfl

@[simp]
theorem Use.cast_cast {e e' e'' : STm L A}
  (he₁ : e = e') (he₂ : e' = e'')
  (u : Use e) :
  (u.cast he₁).cast he₂ = u.cast (he₁.trans he₂)
  := by cases he₁; cases he₂; rfl

@[simp]
theorem Use.cast_atom {e e' : STm L A} (he : e = e') (u : Use e) :
  (u.cast he).atom = u.atom := by cases he; rfl

@[simp]
def Use.arity?
  {e : STm L A} : Use e → Option Arity
  | .sym _ => none
  | .op (arity := arity) _ _ => some arity

end STm

end Isotope
