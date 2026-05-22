import Mathlib.Data.Nat.Notation
import Mathlib.Data.Fintype.Basic
import Mathlib.Logic.Encodable.Basic

namespace Isotope

universe uargs uix

class UArgs (Arity : Type uargs) where
  Ix : Arity -> Type uix

namespace UArgs

variable {Arity L R : Type uargs}
  [inst : UArgs Arity]
  [instL : UArgs L] [instR : UArgs R]

inductive Ix? : Option Arity → Type _
  | mk {args : Arity} : Ix args → Ix? (some args)

inductive IxN : Type _
  | mk {args : Arity} : Ix args → IxN

instance instSum : UArgs (Sum L R) where
  Ix e := e.elim UArgs.Ix UArgs.Ix

instance instProd : UArgs (Prod L R) where
  Ix e := Sum (UArgs.Ix e.1) (UArgs.Ix e.2)

end UArgs

class Args (Arity : Type uargs) extends UArgs Arity where
  posList : ∀ args : Arity, List (Ix args)
  posList_nodup : ∀ args, (posList args).Nodup
  maxPos : Arity -> ℕ := fun args => (posList args).length
  length_posList_eq_maxPos : ∀ args,(posList args).length = maxPos args := by simp
  ixPos : ∀ {args : Arity}, Ix args -> ℕ
  ixPos_lt_length : ∀ {args : Arity} (i : Ix args), ixPos i < (posList args).length
  posList_getElem_ixPos : ∀ args (i : Ix args), (posList args)[ixPos i]'(ixPos_lt_length i) = i

attribute [simp]
  Args.ixPos_lt_length
  Args.posList_getElem_ixPos

namespace Args

export UArgs (Ix Ix?)

class IxFin (Arity : Type uargs) [inst : Args Arity] where
  finType : ∀ (args : Arity), Fintype (Ix args)

section PosList

variable {Arity : Type uargs} [inst : Args Arity] {args : Arity}

@[simp]
theorem ixPos_lt_maxPos (i : Ix args) : ixPos i < maxPos args
  := by rw [<-inst.length_posList_eq_maxPos args]; apply inst.ixPos_lt_length

theorem posList_getElem?_ixPos (i : Ix args) :
  (posList args)[ixPos i]? = some i
  := by simp

@[simp]
theorem mem_posList (i : Ix args) :
  i ∈ posList args
  := by rw [← posList_getElem_ixPos args i]; apply List.getElem_mem

@[simp]
theorem ixPos_inj {i j : Ix args}
  (h : ixPos i = ixPos j) : i = j
  := by
  have h' : (posList args)[ixPos i]? = (posList args)[ixPos j]? := by rw [h]
  convert h'
  simp

theorem ixPos_eq_iff {i j : Ix args}
  : (ixPos i = ixPos j) ↔ i = j
  := ⟨fun h => ixPos_inj h, fun h => by rw [h]⟩

instance ixDecidableEq {args : Arity} : DecidableEq (Ix args)
  := fun _ _ => decidable_of_iff _ ixPos_eq_iff

def posFinset (args : Arity) : Finset (Ix args) :=
  (posList args).toFinset

@[simp]
theorem posFinset_complete (i : Ix args) : i ∈ posFinset args
  := by simp [posFinset]

instance instIxFin : Args.IxFin Arity where
  finType args := {
      elems := (posFinset args)
      complete := by simp
    }

end PosList

instance instNat : Args ℕ where
  Ix := Fin
  posList n := List.finRange n
  posList_nodup n := List.nodup_finRange n
  maxPos n := n
  ixPos i := i
  ixPos_lt_length i := by simp
  posList_getElem_ixPos n i := by simp

instance instFin {N} : Args (Fin N) where
  Ix n := Fin n
  posList n := List.finRange n
  posList_nodup n := List.nodup_finRange n
  maxPos n := n
  ixPos i := i
  ixPos_lt_length i := by simp
  posList_getElem_ixPos n i := by simp

instance instEmpty : Args Empty where
  Ix _ := Empty
  posList _ := []
  posList_nodup _ := by simp
  maxPos _ := 0
  posList_getElem_ixPos _ i := by cases i
  ixPos _ := 0
  ixPos_lt_length i := by cases i

universe usrc utrg

class Hom
  (Src : Type usrc) (Trg : Type utrg)
  [srcArity : Args Src] [trgArity : Args Trg] where
  mapArgs : Src -> Trg
  mapIx : ∀ {args : Src}, Ix args -> Ix (mapArgs args)

instance Hom.finToNat {N} : Hom (Fin N) ℕ where
  mapArgs n := n
  mapIx i := i

end Args


end Isotope
