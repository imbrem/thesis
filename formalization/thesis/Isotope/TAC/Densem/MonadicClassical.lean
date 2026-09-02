import Isotope.TAC.Densem.Phi

/-! # Monadic agreement of phi-free classical SSA and densem -/

namespace Isotope.TAC.Densem.Phi.Monadic

variable {ν φ κ : Type} {m : Type → Type}
  {M : Isotope.TAC.Densem.Monadic.Model φ m}

/-- The distinguished polymorphic failure is a left zero for sequencing.
This is deliberately explicit: an arbitrary inhabitant of every `m α` need
not behave like failure. -/
class LawfulFailure [Monad m]
    (M : Isotope.TAC.Densem.Monadic.Model φ m) : Prop where
  fail_bind {A B : Type} (f : A → m B) : (M.fail : m A) >>= f = M.fail

@[simp] theorem assignments_nil [Monad m] [DecidableEq κ]
    (M : Isotope.TAC.Densem.Monadic.Model φ m)
    (ρ : Isotope.TAC.Densem.Monadic.Env M ν)
    (pred : Isotope.TAC.Classical.BlockId κ) :
    assignments M ρ pred [] = pure [] := rfl

theorem enter_phiFree [Monad m] [LawfulMonad m] [DecidableEq ν] [DecidableEq κ]
    (M : Isotope.TAC.Densem.Monadic.Model φ m)
    (ρ : Isotope.TAC.Densem.Monadic.Env M ν)
    (pred : Isotope.TAC.Classical.BlockId κ)
    (b : Isotope.TAC.Classical.Block ν φ κ) (h : b.phis = []) :
    enter M ρ pred b = Isotope.TAC.Densem.Monadic.Block.denote M ρ
      (Isotope.TAC.Densem.Classical.block b) := by
  cases b
  change _ = [] at h
  cases h
  simp [enter, assignments, install]

theorem lookup_translate [DecidableEq κ]
    (g : Isotope.TAC.Classical.CFG ν φ κ)
    (h : Isotope.TAC.Densem.Classical.PhiFree g) (label : κ) :
    Isotope.TAC.Densem.Monadic.lookup (Isotope.TAC.Densem.Classical.cfg g h) label =
      (Isotope.TAC.Densem.Phi.lookup g label).map Isotope.TAC.Densem.Classical.block := by
  unfold Isotope.TAC.Densem.Monadic.lookup Isotope.TAC.Densem.Phi.lookup
    Isotope.TAC.Densem.Classical.cfg
  induction g.blocks with
  | nil => rfl
  | cons p ps ih =>
      simp only [List.map_cons, List.find?_cons]
      split <;> simp_all

def eraseState : Isotope.TAC.Densem.Monadic.Env M ν ×
    Isotope.TAC.Classical.BlockId κ × κ →
    Isotope.TAC.Densem.Monadic.Env M ν × κ
  | (ρ, _, label) => (ρ, label)

theorem step_phiFree [Monad m] [LawfulMonad m]
    [DecidableEq ν] [DecidableEq κ]
    (M : Isotope.TAC.Densem.Monadic.Model φ m)
    [LawfulFailure M]
    (g : Isotope.TAC.Classical.CFG ν φ κ)
    (h : Isotope.TAC.Densem.Classical.PhiFree g)
    (state : Isotope.TAC.Densem.Monadic.Env M ν ×
      Isotope.TAC.Classical.BlockId κ × κ) :
    step M g state =
      Isotope.TAC.Densem.Monadic.CFG.step M
        (Isotope.TAC.Densem.Classical.cfg g h) (eraseState state) >>= fun result =>
        pure (Sum.map id (fun next => (next.1, .named state.2.2, next.2)) result) := by
  rcases state with ⟨ρ, pred, label⟩
  simp only [step, eraseState, Isotope.TAC.Densem.Monadic.CFG.step]
  rw [lookup_translate]
  cases hb : Isotope.TAC.Densem.Phi.lookup g label with
  | none =>
      simp only [Option.map_none]
      exact (LawfulFailure.fail_bind _).symm
  | some b =>
      simp only [Option.map_some]
      rw [enter_phiFree M ρ pred b
        (Isotope.TAC.Densem.Phi.lookup_phiFree g h label b hb)]
      simp only [bind_assoc]
      apply congrArg (fun k => Isotope.TAC.Densem.Monadic.Block.denote M ρ
        (Isotope.TAC.Densem.Classical.block b) >>= k)
      funext p
      rcases p with ⟨ρ', exit⟩
      cases exit <;> simp

theorem iter_phiFree [Monad m] [LawfulMonad m] [Isotope.Elgot.Iterate m]
    [Isotope.Elgot.LawfulElgotMonad m] [DecidableEq ν] [DecidableEq κ]
    (M : Isotope.TAC.Densem.Monadic.Model φ m) [LawfulFailure M]
    (g : Isotope.TAC.Classical.CFG ν φ κ)
    (h : Isotope.TAC.Densem.Classical.PhiFree g)
    (state : Isotope.TAC.Densem.Monadic.Env M ν ×
      Isotope.TAC.Classical.BlockId κ × κ) :
    Isotope.Elgot.iter (step M g) state =
      Isotope.Elgot.iter
        (Isotope.TAC.Densem.Monadic.CFG.step M
          (Isotope.TAC.Densem.Classical.cfg g h)) (eraseState state) := by
  let f := step M g
  let q := Isotope.TAC.Densem.Monadic.CFG.step M
    (Isotope.TAC.Densem.Classical.cfg g h)
  have comm : Isotope.Elgot.kcomp f
      (Isotope.Elgot.liftPure (Sum.map id eraseState)) =
      Isotope.Elgot.kcomp (Isotope.Elgot.liftPure eraseState) q := by
    funext s
    simp only [Isotope.Elgot.kcomp]
    rw [show f s = q (eraseState s) >>= fun result =>
        pure (Sum.map id (fun next => (next.1, .named s.2.2, next.2)) result) from
      step_phiFree M g h s]
    simp [Isotope.Elgot.kcomp, Isotope.Elgot.liftPure, q, Function.comp_def,
      bind_assoc]
    have hid : (fun a : M.Val ⊕
        (Isotope.TAC.Densem.Monadic.Env M ν × κ) =>
          Sum.map (fun x : M.Val => x)
            (fun x : Isotope.TAC.Densem.Monadic.Env M ν × κ => (x.1, x.2)) a) =
        id := by
      funext a
      cases a <;> rfl
    simp only [eraseState]
    rw [hid]
    simp
  have hu := Isotope.Elgot.LawfulElgotMonad.uniformity f q eraseState comm
  change Isotope.Elgot.iter f state = Isotope.Elgot.iter q (eraseState state)
  rw [hu]
  simp [Isotope.Elgot.kcomp, Isotope.Elgot.liftPure, Function.comp_def]

/-- Removing empty phi lists commutes with the complete-Elgot monadic
semantics of the whole CFG. -/
theorem denote_phiFree [Monad m] [LawfulMonad m] [Isotope.Elgot.Iterate m]
    [Isotope.Elgot.LawfulElgotMonad m] [DecidableEq ν] [DecidableEq κ]
    (M : Isotope.TAC.Densem.Monadic.Model φ m) [LawfulFailure M]
    (g : Isotope.TAC.Classical.CFG ν φ κ)
    (h : Isotope.TAC.Densem.Classical.PhiFree g)
    (ρ : Isotope.TAC.Densem.Monadic.Env M ν) :
    denote M g ρ = Isotope.TAC.Densem.Monadic.CFG.denote M
      (Isotope.TAC.Densem.Classical.cfg g h) ρ := by
  unfold denote Isotope.TAC.Densem.Monadic.CFG.denote
  rw [enter_phiFree M ρ .entry g.entry h.entry]
  apply bind_congr
  intro p
  rcases p with ⟨ρ', exit⟩
  cases exit with
  | «return» => rfl
  | branch label => exact iter_phiFree M g h (ρ', .entry, label)

end Isotope.TAC.Densem.Phi.Monadic
