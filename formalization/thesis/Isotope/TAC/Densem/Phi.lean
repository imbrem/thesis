import Isotope.TAC.Densem.Classical
import Isotope.TAC.Densem.Monadic

/-! # Predecessor-sensitive semantics of classical phi nodes -/

namespace Isotope.TAC.Densem.Phi

namespace C
abbrev Value := Isotope.TAC.Classical.Value
abbrev BlockId := Isotope.TAC.Classical.BlockId
abbrev Incoming := Isotope.TAC.Classical.Incoming
abbrev Phi := Isotope.TAC.Classical.Phi
abbrev Block := Isotope.TAC.Classical.Block
abbrev CFG := Isotope.TAC.Classical.CFG
end C

/-- Select the value supplied by the uniquely matching predecessor edge. -/
def incoming [DecidableEq κ] (pred : C.BlockId κ)
    (xs : List (C.Incoming ν κ)) : Option (C.Value ν) :=
  (xs.find? fun x => x.predecessor = pred).map Isotope.TAC.Classical.Incoming.value

def assignments [DecidableEq κ] (M : Model φ) (ρ : Env M ν)
    (pred : C.BlockId κ) : List (C.Phi ν κ) → Option (List (ν × M.Val))
  | [] => some []
  | p :: ps => do
      let a ← incoming pred p.incoming
      let v ← Isotope.TAC.Densem.Classical.Executable.valueDenote M ρ a
      return (p.dst, v) :: (← assignments M ρ pred ps)

def install [DecidableEq ν] (ρ : Env M ν) : List (ν × M.Val) → Env M ν
  | [] => ρ
  | (x, a) :: xs => install (Env.set ρ x a) xs

def enter [DecidableEq ν] [DecidableEq κ] (M : Model φ) (ρ : Env M ν)
    (pred : C.BlockId κ) (b : C.Block ν φ κ) : Option (Env M ν × Exit κ M.Val) := do
  let xs ← assignments M ρ pred b.phis
  Isotope.TAC.Densem.Classical.Executable.blockDenote M (install ρ xs) b

@[simp] theorem enter_phiFree [DecidableEq ν] [DecidableEq κ]
    (M : Model φ) (ρ : Env M ν) (pred : C.BlockId κ) (b : C.Block ν φ κ)
    (h : b.phis = []) : enter M ρ pred b =
      Isotope.TAC.Densem.Classical.Executable.blockDenote M ρ b := by
  cases b
  change _ = [] at h
  cases h
  rfl

def lookup [DecidableEq κ] (g : C.CFG ν φ κ) (ℓ : κ) : Option (C.Block ν φ κ) :=
  (g.blocks.find? fun p => p.1 = ℓ).map Prod.snd

def continueFuel [DecidableEq ν] [DecidableEq κ] (M : Model φ) (g : C.CFG ν φ κ) :
    Nat → Env M ν → C.BlockId κ → Exit κ M.Val → Option M.Val
  | _, _, _, .return a => some a
  | 0, _, _, .branch _ => none
  | fuel + 1, ρ, pred, .branch ℓ => do
      let b ← lookup g ℓ
      let (ρ', e) ← enter M ρ pred b
      continueFuel M g fuel ρ' (.named ℓ) e

def runFuel [DecidableEq ν] [DecidableEq κ] (M : Model φ) (g : C.CFG ν φ κ) :
    Nat → Env M ν → Option M.Val
  | 0, _ => none
  | fuel + 1, ρ => do
      let (ρ', e) ← enter M ρ .entry g.entry
      continueFuel M g fuel ρ' .entry e

theorem lookup_phiFree [DecidableEq κ] (g : C.CFG ν φ κ)
    (h : Isotope.TAC.Densem.Classical.PhiFree g) (ℓ : κ) (b : C.Block ν φ κ)
    (hb : lookup g ℓ = some b) : b.phis = [] := by
  unfold lookup at hb
  rw [Option.map_eq_some_iff] at hb
  rcases hb with ⟨p, hp, rfl⟩
  exact h.blocks p (List.mem_of_find?_eq_some hp)

theorem lookup_translate [DecidableEq κ] (g : C.CFG ν φ κ)
    (h : Isotope.TAC.Densem.Classical.PhiFree g) (ℓ : κ) :
    CFG.lookup (Isotope.TAC.Densem.Classical.cfg g h) ℓ =
      (lookup g ℓ).map Isotope.TAC.Densem.Classical.block := by
  unfold CFG.lookup Isotope.TAC.Densem.Classical.cfg lookup
  induction g.blocks with
  | nil => rfl
  | cons p ps ih => simp only [List.map_cons, List.find?_cons]; split <;> simp_all

theorem continueFuel_phiFree [DecidableEq ν] [DecidableEq κ]
    (M : Model φ) (g : C.CFG ν φ κ) (h : Isotope.TAC.Densem.Classical.PhiFree g)
    (fuel : Nat) (ρ : Env M ν) (pred : C.BlockId κ) (e : Exit κ M.Val) :
    continueFuel M g fuel ρ pred e =
      CFG.continueFuel M (Isotope.TAC.Densem.Classical.cfg g h) fuel ρ e := by
  induction fuel generalizing ρ pred e with
  | zero => cases e <;> rfl
  | succ fuel ih =>
      cases e with
      | «return» a => rfl
      | branch ℓ =>
        simp only [continueFuel, CFG.continueFuel]
        rw [lookup_translate]
        cases hb : lookup g ℓ with
        | none => rfl
        | some b =>
          dsimp
          rw [enter_phiFree M ρ pred b (lookup_phiFree g h ℓ b hb)]
          rw [Isotope.TAC.Densem.Classical.Executable.block_commute]
          cases hp : Isotope.TAC.Densem.Classical.Executable.blockDenote M ρ b with
          | none => rfl
          | some p =>
            cases p with
            | mk ρ' e => simpa only [Option.bind_some] using ih ρ' (.named ℓ) e

theorem runFuel_phiFree [DecidableEq ν] [DecidableEq κ]
    (M : Model φ) (g : C.CFG ν φ κ) (h : Isotope.TAC.Densem.Classical.PhiFree g)
    (fuel : Nat) (ρ : Env M ν) :
    runFuel M g fuel ρ =
      CFG.runFuel M (Isotope.TAC.Densem.Classical.cfg g h) fuel ρ := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      simp only [runFuel, CFG.runFuel, Isotope.TAC.Densem.Classical.cfg]
      rw [enter_phiFree M ρ .entry g.entry h.entry]
      rw [Isotope.TAC.Densem.Classical.Executable.block_commute]
      cases hp : Isotope.TAC.Densem.Classical.Executable.blockDenote M ρ g.entry with
      | none => rfl
      | some p =>
        cases p with
        | mk ρ' e => simpa only [Option.bind_some] using
            continueFuel_phiFree M g h fuel ρ' .entry e

namespace Monadic

def assignments [Monad m] [DecidableEq κ] (M : Isotope.TAC.Densem.Monadic.Model φ m)
    (ρ : Isotope.TAC.Densem.Monadic.Env M ν) (pred : C.BlockId κ) :
    List (C.Phi ν κ) → m (List (ν × M.Val))
  | [] => pure []
  | p :: ps => match incoming pred p.incoming with
      | none => M.fail
      | some a => do
          let v ← Isotope.TAC.Densem.Monadic.Value.denote M ρ
            (Isotope.TAC.Densem.Classical.value a)
          return (p.dst, v) :: (← assignments M ρ pred ps)

def install [DecidableEq ν] (ρ : Isotope.TAC.Densem.Monadic.Env M ν) :
    List (ν × M.Val) → Isotope.TAC.Densem.Monadic.Env M ν
  | [] => ρ
  | (x, a) :: xs => install (Isotope.TAC.Densem.Monadic.Env.set ρ x a) xs

def enter [Monad m] [DecidableEq ν] [DecidableEq κ]
    (M : Isotope.TAC.Densem.Monadic.Model φ m)
    (ρ : Isotope.TAC.Densem.Monadic.Env M ν) (pred : C.BlockId κ)
    (b : C.Block ν φ κ) : m (Isotope.TAC.Densem.Monadic.Env M ν × Exit κ M.Val) := do
  let xs ← assignments M ρ pred b.phis
  Isotope.TAC.Densem.Monadic.Block.denote M (install ρ xs)
    (Isotope.TAC.Densem.Classical.block b)

def step [Monad m] [DecidableEq ν] [DecidableEq κ]
    (M : Isotope.TAC.Densem.Monadic.Model φ m) (g : C.CFG ν φ κ) :
    Isotope.TAC.Densem.Monadic.Env M ν × C.BlockId κ × κ →
      m (M.Val ⊕ (Isotope.TAC.Densem.Monadic.Env M ν × C.BlockId κ × κ))
  | (ρ, pred, ℓ) => match lookup g ℓ with
      | none => M.fail
      | some b => do
          let (ρ', e) ← enter M ρ pred b
          match e with
          | .return a => pure (.inl a)
          | .branch k => pure (.inr (ρ', .named ℓ, k))

def denote [Monad m] [Isotope.Elgot.Iterate m] [DecidableEq ν] [DecidableEq κ]
    (M : Isotope.TAC.Densem.Monadic.Model φ m) (g : C.CFG ν φ κ)
    (ρ : Isotope.TAC.Densem.Monadic.Env M ν) : m M.Val := do
  let (ρ', e) ← enter M ρ .entry g.entry
  match e with
  | .return a => pure a
  | .branch ℓ => Isotope.Elgot.iter (step M g) (ρ', .entry, ℓ)

end Monadic
end Isotope.TAC.Densem.Phi
