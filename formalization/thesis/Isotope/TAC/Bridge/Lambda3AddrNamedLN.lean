import Isotope.TAC.Bridge.Lambda3Addr
import Isotope.LambdaIter.Named.ToLocallyNameless

/-! # Named and locally nameless lambda three-address code

Unlike `Densem.Block`, the presentations here make the lexical scope of an
instruction destination part of the syntax.  The raw de Bruijn presentation
is accompanied by an intrinsic scoping witness; closed locally nameless
syntax is exactly equivalent to scoped raw syntax.
-/

namespace Isotope.TAC.Bridge.Lambda3AddrNamedLN

open Isotope.TAC

universe u v w

namespace Named

abbrev Binder (ν : Type u) := Option ν

inductive Value (ν : Type u) where
  | var (x : ν)
  | pair (left right : Value ν)
  | unit
  deriving Repr, DecidableEq

inductive Operand (ν : Type u) (φ : Type v) where
  | value (v : Value ν)
  | op (f : φ) (arg : Value ν)
  | inl (arg : Value ν)
  | inr (arg : Value ν)
  | abort (arg : Value ν)
  deriving Repr, DecidableEq

inductive Terminator (ν : Type u) (φ : Type v) (κ : Type w) where
  | br (label : κ)
  | ret (value : Value ν)
  | ite (discr : Operand ν φ)
      (left right : Terminator ν φ κ)
  deriving Repr, DecidableEq

/-- Instruction destinations scope precisely over the remaining block. -/
inductive Block (ν : Type u) (φ : Type v) (κ : Type w) where
  | terminator (term : Terminator ν φ κ)
  | let₁ (dst : Binder ν) (rhs : Operand ν φ) (rest : Block ν φ κ)
  | let₂ (fst snd : Binder ν) (rhs : Operand ν φ) (rest : Block ν φ κ)
  deriving Repr, DecidableEq

structure CFG (ν : Type u) (φ : Type v) (κ : Type w) where
  entry : Block ν φ κ
  blocks : List (κ × Block ν φ κ)
  deriving Repr, DecidableEq

end Named

namespace LocallyNameless

inductive Value (ν : Type u) : Nat → Type u where
  | fv (x : ν) : Value ν n
  | bv (index : Fin n) : Value ν n
  | pair (left right : Value ν n) : Value ν n
  | unit : Value ν n
  deriving Repr, DecidableEq

inductive Operand (ν : Type u) (φ : Type v) : Nat → Type (max u v) where
  | value (v : Value ν n) : Operand ν φ n
  | op (f : φ) (arg : Value ν n) : Operand ν φ n
  | inl (arg : Value ν n) : Operand ν φ n
  | inr (arg : Value ν n) : Operand ν φ n
  | abort (arg : Value ν n) : Operand ν φ n
  deriving Repr, DecidableEq

inductive Terminator (ν : Type u) (φ : Type v) (κ : Type w) :
    Nat → Type (max u v w) where
  | br (label : κ) : Terminator ν φ κ n
  | ret (value : Value ν n) : Terminator ν φ κ n
  | ite (discr : Operand ν φ n)
      (left right : Terminator ν φ κ n) : Terminator ν φ κ n
  deriving Repr, DecidableEq

/-- The index is the number of enclosing instruction destinations. -/
inductive Block (ν : Type u) (φ : Type v) (κ : Type w) :
    Nat → Type (max u v w) where
  | terminator (term : Terminator ν φ κ n) : Block ν φ κ n
  | let₁ (rhs : Operand ν φ n) (rest : Block ν φ κ (n + 1)) : Block ν φ κ n
  | let₂ (rhs : Operand ν φ n) (rest : Block ν φ κ (n + 1 + 1)) : Block ν φ κ n
  deriving Repr, DecidableEq

structure CFG (ν : Type u) (φ : Type v) (κ : Type w) (n : Nat) where
  entry : Block ν φ κ n
  blocks : List (κ × Block ν φ κ n)
  deriving Repr, DecidableEq

end LocallyNameless

namespace Named.ToLocallyNameless

abbrev Scope := LambdaIter.Named.ToLocallyNameless.Scope

def value [DecidableEq ν] (ρ : Scope ν n) :
    Named.Value ν → LocallyNameless.Value ν n
  | .var x => match ρ.resolve x with
    | .inl i => .bv i
    | .inr y => .fv y
  | .pair l r => .pair (value ρ l) (value ρ r)
  | .unit => .unit

def operand [DecidableEq ν] (ρ : Scope ν n) :
    Named.Operand ν φ → LocallyNameless.Operand ν φ n
  | .value v => .value (value ρ v)
  | .op f v => .op f (value ρ v)
  | .inl v => .inl (value ρ v)
  | .inr v => .inr (value ρ v)
  | .abort v => .abort (value ρ v)

def terminator [DecidableEq ν] (ρ : Scope ν n) :
    Named.Terminator ν φ κ → LocallyNameless.Terminator ν φ κ n
  | .br label => .br label
  | .ret v => .ret (value ρ v)
  | .ite discr l r => .ite (operand ρ discr) (terminator ρ l) (terminator ρ r)

def block [DecidableEq ν] (ρ : Scope ν n) :
    Named.Block ν φ κ → LocallyNameless.Block ν φ κ n
  | .terminator term => .terminator (terminator ρ term)
  | .let₁ dst rhs rest => .let₁ (operand ρ rhs) (block (.push dst ρ) rest)
  | .let₂ fst snd rhs rest =>
      .let₂ (operand ρ rhs) (block (.push snd (.push fst ρ)) rest)

def closed [DecidableEq ν] (b : Named.Block ν φ κ) :
    LocallyNameless.Block ν φ κ 0 := block .nil b

def cfg [DecidableEq ν] (ρ : Scope ν n) (g : Named.CFG ν φ κ) :
    LocallyNameless.CFG ν φ κ n where
  entry := block ρ g.entry
  blocks := g.blocks.map fun pair => (pair.1, block ρ pair.2)

def closedCFG [DecidableEq ν] (g : Named.CFG ν φ κ) :
    LocallyNameless.CFG ν φ κ 0 := cfg .nil g

/-- Alpha-equivalence is equality after forgetting binder spelling. -/
def AlphaEq [DecidableEq ν] (left right : Named.Block ν φ κ) : Prop :=
  closed left = closed right

def CFG.AlphaEq [DecidableEq ν] (left right : Named.CFG ν φ κ) : Prop :=
  closedCFG left = closedCFG right

theorem CFG.AlphaEq.semantic {α : Sort*} [DecidableEq ν]
    (sem : LocallyNameless.CFG ν φ κ 0 → α)
    {left right : Named.CFG ν φ κ} (h : CFG.AlphaEq left right) :
    sem (closedCFG left) = sem (closedCFG right) := congrArg sem h

@[refl] theorem AlphaEq.refl [DecidableEq ν] (b : Named.Block ν φ κ) :
    AlphaEq b b := rfl

@[symm] theorem AlphaEq.symm [DecidableEq ν] {a b : Named.Block ν φ κ}
    (h : AlphaEq a b) : AlphaEq b a := Eq.symm h

@[trans] theorem AlphaEq.trans [DecidableEq ν] {a b c : Named.Block ν φ κ}
    (hab : AlphaEq a b) (hbc : AlphaEq b c) : AlphaEq a c := Eq.trans hab hbc

end Named.ToLocallyNameless

/-! Raw de Bruijn syntax deliberately uses `Nat`; scoping is not baked into
the raw tree, matching the existing `LambdaSSA` presentation. -/
namespace DeBruijn

inductive Value where
  | var (index : Nat)
  | pair (left right : Value)
  | unit
  deriving Repr, DecidableEq

inductive Operand (φ : Type v) where
  | value (v : Value)
  | op (f : φ) (arg : Value)
  | inl (arg : Value)
  | inr (arg : Value)
  | abort (arg : Value)
  deriving Repr, DecidableEq

inductive Terminator (φ : Type v) (κ : Type w) where
  | br (label : κ)
  | ret (value : Value)
  | ite (discr : Operand φ)
      (left right : Terminator φ κ)
  deriving Repr, DecidableEq

inductive Block (φ : Type v) (κ : Type w) where
  | terminator (term : Terminator φ κ)
  | let₁ (rhs : Operand φ) (rest : Block φ κ)
  | let₂ (rhs : Operand φ) (rest : Block φ κ)
  deriving Repr, DecidableEq

structure CFG (φ : Type v) (κ : Type w) where
  entry : Block φ κ
  blocks : List (κ × Block φ κ)
  deriving Repr, DecidableEq

inductive Value.Scoped : Nat → Value → Type where
  | var (index : Nat) (bound : index < n) : Scoped n (.var index)
  | pair : Scoped n l → Scoped n r → Scoped n (.pair l r)
  | unit : Scoped n .unit

inductive Operand.Scoped : Nat → Operand φ → Type _ where
  | value : Value.Scoped n v → Scoped n (.value v)
  | op : Value.Scoped n v → Scoped n (.op f v)
  | inl : Value.Scoped n v → Scoped n (.inl v)
  | inr : Value.Scoped n v → Scoped n (.inr v)
  | abort : Value.Scoped n v → Scoped n (.abort v)

inductive Terminator.Scoped : Nat → Terminator φ κ → Type _ where
  | br (label : κ) : Scoped n (.br label)
  | ret : Value.Scoped n v → Scoped n (.ret v)
  | ite {discr : Operand φ} {l r : Terminator φ κ} :
      Operand.Scoped n discr → Scoped n l → Scoped n r →
      Scoped n (.ite discr l r)

inductive Block.Scoped : Nat → Block φ κ → Type _ where
  | terminator {term : Terminator φ κ} :
      Terminator.Scoped n term → Scoped n (.terminator term)
  | let₁ {rhs : Operand φ} {rest : Block φ κ} :
      Operand.Scoped n rhs → Scoped (n + 1) rest →
      Scoped n (.let₁ rhs rest)
  | let₂ {rhs : Operand φ} {rest : Block φ κ} :
      Operand.Scoped n rhs → Scoped (n + 1 + 1) rest →
      Scoped n (.let₂ rhs rest)

end DeBruijn

namespace LocallyNameless.ToDeBruijn

def eraseValue : LocallyNameless.Value Empty n → DeBruijn.Value
  | .fv x => Empty.elim x
  | .bv i => .var i
  | .pair l r => .pair (eraseValue l) (eraseValue r)
  | .unit => .unit

def eraseOperand : LocallyNameless.Operand Empty φ n → DeBruijn.Operand φ
  | .value v => .value (eraseValue v)
  | .op f v => .op f (eraseValue v)
  | .inl v => .inl (eraseValue v)
  | .inr v => .inr (eraseValue v)
  | .abort v => .abort (eraseValue v)

def eraseTerminator : LocallyNameless.Terminator Empty φ κ n →
    DeBruijn.Terminator φ κ
  | .br label => .br label
  | .ret v => .ret (eraseValue v)
  | .ite discr l r => .ite (eraseOperand discr)
      (eraseTerminator l) (eraseTerminator r)

def eraseBlock : LocallyNameless.Block Empty φ κ n → DeBruijn.Block φ κ
  | .terminator term => .terminator (eraseTerminator term)
  | .let₁ rhs rest => .let₁ (eraseOperand rhs) (eraseBlock rest)
  | .let₂ rhs rest => .let₂ (eraseOperand rhs) (eraseBlock rest)

def eraseCFG (g : LocallyNameless.CFG Empty φ κ n) : DeBruijn.CFG φ κ where
  entry := eraseBlock g.entry
  blocks := g.blocks.map fun pair => (pair.1, eraseBlock pair.2)

def scopeValue : (v : LocallyNameless.Value Empty n) →
    DeBruijn.Value.Scoped n (eraseValue v)
  | .fv x => Empty.elim x
  | .bv i => .var i i.isLt
  | .pair l r => .pair (scopeValue l) (scopeValue r)
  | .unit => .unit

def scopeOperand : (o : LocallyNameless.Operand Empty φ n) →
    DeBruijn.Operand.Scoped n (eraseOperand o)
  | .value v => .value (scopeValue v)
  | .op _ v => .op (scopeValue v)
  | .inl v => .inl (scopeValue v)
  | .inr v => .inr (scopeValue v)
  | .abort v => .abort (scopeValue v)

def scopeTerminator : (t : LocallyNameless.Terminator Empty φ κ n) →
    DeBruijn.Terminator.Scoped n (eraseTerminator t)
  | .br label => .br label
  | .ret v => .ret (scopeValue v)
  | .ite discr l r => .ite (scopeOperand discr) (scopeTerminator l) (scopeTerminator r)

def scopeBlock : (b : LocallyNameless.Block Empty φ κ n) →
    DeBruijn.Block.Scoped n (eraseBlock b)
  | .terminator term => .terminator (scopeTerminator term)
  | .let₁ rhs rest => .let₁ (scopeOperand rhs) (scopeBlock rest)
  | .let₂ rhs rest => .let₂ (scopeOperand rhs) (scopeBlock rest)

def embedValue : {v : DeBruijn.Value} → DeBruijn.Value.Scoped n v →
    LocallyNameless.Value Empty n
  | _, .var i hi => .bv ⟨i, hi⟩
  | _, .pair l r => .pair (embedValue l) (embedValue r)
  | _, .unit => .unit

def embedOperand : {o : DeBruijn.Operand φ} → DeBruijn.Operand.Scoped n o →
    LocallyNameless.Operand Empty φ n
  | _, .value v => .value (embedValue v)
  | _, .op (f := f) v => .op f (embedValue v)
  | _, .inl v => .inl (embedValue v)
  | _, .inr v => .inr (embedValue v)
  | _, .abort v => .abort (embedValue v)

def embedTerminator : {t : DeBruijn.Terminator φ κ} →
    DeBruijn.Terminator.Scoped n t → LocallyNameless.Terminator Empty φ κ n
  | _, .br label => .br label
  | _, .ret v => .ret (embedValue v)
  | _, .ite hd hl hr => .ite (embedOperand hd) (embedTerminator hl) (embedTerminator hr)

def embedBlock : {b : DeBruijn.Block φ κ} → DeBruijn.Block.Scoped n b →
    LocallyNameless.Block Empty φ κ n
  | _, .terminator term => .terminator (embedTerminator term)
  | _, .let₁ rhs rest => .let₁ (embedOperand rhs) (embedBlock rest)
  | _, .let₂ rhs rest => .let₂ (embedOperand rhs) (embedBlock rest)

theorem embedValue_irrel {v : DeBruijn.Value}
    (h k : DeBruijn.Value.Scoped n v) : embedValue h = embedValue k := by
  induction h with
  | var i hi =>
      cases k with
      | var _ hj => rw [Subsingleton.elim hi hj]
  | pair hl hr il ir =>
      cases k with
      | pair kl kr => exact congrArg₂ LocallyNameless.Value.pair (il kl) (ir kr)
  | unit => cases k; rfl

theorem embedOperand_irrel {o : DeBruijn.Operand φ}
    (h k : DeBruijn.Operand.Scoped n o) : embedOperand h = embedOperand k := by
  cases h <;> cases k <;> simp only [embedOperand] <;>
    congr 1 <;> exact embedValue_irrel _ _

theorem embedTerminator_irrel {t : DeBruijn.Terminator φ κ}
    (h k : DeBruijn.Terminator.Scoped n t) :
    embedTerminator h = embedTerminator k := by
  induction h with
  | br label => cases k; rfl
  | ret hv =>
      cases k with
      | ret kv => exact congrArg LocallyNameless.Terminator.ret (embedValue_irrel hv kv)
  | ite hd hl hr il ir =>
      cases k with
      | ite kd kl kr =>
          simp only [embedTerminator]
          rw [embedOperand_irrel hd kd, il kl, ir kr]

theorem embedBlock_irrel {b : DeBruijn.Block φ κ}
    (h k : DeBruijn.Block.Scoped n b) : embedBlock h = embedBlock k := by
  induction h with
  | terminator ht =>
      cases k with
      | terminator kt =>
          simp only [embedBlock]
          rw [embedTerminator_irrel ht kt]
  | let₁ ho hb ih =>
      cases k with
      | let₁ ko kb =>
          simp only [embedBlock]
          rw [embedOperand_irrel ho ko, ih kb]
  | let₂ ho hb ih =>
      cases k with
      | let₂ ko kb =>
          simp only [embedBlock]
          rw [embedOperand_irrel ho ko, ih kb]

@[simp] theorem eraseValue_embedValue : {v : DeBruijn.Value} →
    (h : DeBruijn.Value.Scoped n v) → eraseValue (embedValue h) = v
  | _, .var _ _ => rfl
  | _, .pair l r => by simp [embedValue, eraseValue, eraseValue_embedValue l,
      eraseValue_embedValue r]
  | _, .unit => rfl

@[simp] theorem eraseOperand_embedOperand : {o : DeBruijn.Operand φ} →
    (h : DeBruijn.Operand.Scoped n o) → eraseOperand (embedOperand h) = o
  | _, .value v | _, .op v | _, .inl v | _, .inr v | _, .abort v => by
      simp [embedOperand, eraseOperand, eraseValue_embedValue v]

@[simp] theorem eraseTerminator_embedTerminator : {t : DeBruijn.Terminator φ κ} →
    (h : DeBruijn.Terminator.Scoped n t) → eraseTerminator (embedTerminator h) = t
  | _, .br _ => rfl
  | _, .ret v => by simp [embedTerminator, eraseTerminator]
  | _, .ite hd hl hr => by
      simp [embedTerminator, eraseTerminator, eraseTerminator_embedTerminator hl,
        eraseTerminator_embedTerminator hr]

@[simp] theorem eraseBlock_embedBlock : {b : DeBruijn.Block φ κ} →
    (h : DeBruijn.Block.Scoped n b) → eraseBlock (embedBlock h) = b
  | _, .terminator term => by simp [embedBlock, eraseBlock]
  | _, .let₁ rhs rest | _, .let₂ rhs rest => by
      simp [embedBlock, eraseBlock, eraseBlock_embedBlock rest]

@[simp] theorem embedValue_scopeValue (v : LocallyNameless.Value Empty n) :
    embedValue (scopeValue v) = v := by
  induction v with
  | fv x => exact Empty.elim x
  | bv _ | unit => rfl
  | pair l r il ir => simp [embedValue, scopeValue, il, ir]

@[simp] theorem embedOperand_scopeOperand (o : LocallyNameless.Operand Empty φ n) :
    embedOperand (o := eraseOperand o) (scopeOperand o) = o := by
  cases o <;> simp [embedOperand, scopeOperand]

@[simp] theorem embedTerminator_scopeTerminator
    (t : LocallyNameless.Terminator Empty φ κ n) :
    embedTerminator (t := eraseTerminator t) (scopeTerminator t) = t := by
  induction t <;> simp [embedTerminator, scopeTerminator, *]

@[simp] theorem embedBlock_scopeBlock (b : LocallyNameless.Block Empty φ κ n) :
    embedBlock (b := eraseBlock b) (scopeBlock b) = b := by
  induction b <;> simp [embedBlock, scopeBlock, *]

/-- Closed locally nameless blocks and scoped raw de Bruijn blocks are exact
round trips.  The scoping derivation is hidden by `Nonempty`, as in the
existing lambda-SSA bridge. -/
noncomputable def scopedEquiv : LocallyNameless.Block Empty φ κ n ≃
    {b : DeBruijn.Block φ κ // Nonempty (DeBruijn.Block.Scoped n b)} where
  toFun b := ⟨eraseBlock b, ⟨scopeBlock b⟩⟩
  invFun b := embedBlock b.2.some
  left_inv b := by
    change embedBlock ((⟨scopeBlock b⟩ :
      Nonempty (DeBruijn.Block.Scoped n (eraseBlock b))).some) = b
    calc
      _ = embedBlock (scopeBlock b) := embedBlock_irrel _ _
      _ = b := embedBlock_scopeBlock b
  right_inv b := by
    apply Subtype.ext
    exact eraseBlock_embedBlock b.2.some

/-- A whole raw CFG whose entry and every labelled block are scoped at the
same external-variable depth. -/
structure ScopedCFG (φ : Type v) (κ : Type w) (n : Nat) where
  entry : {b : DeBruijn.Block φ κ // Nonempty (DeBruijn.Block.Scoped n b)}
  blocks : List (κ × {b : DeBruijn.Block φ κ //
    Nonempty (DeBruijn.Block.Scoped n b)})

noncomputable def cfgScopedEquiv : LocallyNameless.CFG Empty φ κ n ≃
    ScopedCFG φ κ n where
  toFun g := {
    entry := scopedEquiv g.entry
    blocks := g.blocks.map fun pair => (pair.1, scopedEquiv pair.2) }
  invFun g := {
    entry := scopedEquiv.symm g.entry
    blocks := g.blocks.map fun pair => (pair.1, scopedEquiv.symm pair.2) }
  left_inv g := by
    cases g with
    | mk entry blocks =>
        change LocallyNameless.CFG.mk (scopedEquiv.symm (scopedEquiv entry))
          (List.map (fun pair => (pair.1, scopedEquiv.symm pair.2))
            (List.map (fun pair => (pair.1, scopedEquiv pair.2)) blocks)) =
          LocallyNameless.CFG.mk entry blocks
        congr 1
        · apply scopedEquiv.left_inv
        · induction blocks with
          | nil => rfl
          | cons pair rest ih =>
              simp only [List.map_cons]
              have hp := scopedEquiv.left_inv pair.2
              change scopedEquiv.symm (scopedEquiv pair.2) = pair.2 at hp
              rw [hp, ih]
  right_inv g := by
    cases g with
    | mk entry blocks =>
        change ScopedCFG.mk (scopedEquiv (scopedEquiv.symm entry))
          (List.map (fun pair => (pair.1, scopedEquiv pair.2))
            (List.map (fun pair => (pair.1, scopedEquiv.symm pair.2)) blocks)) =
          ScopedCFG.mk entry blocks
        congr 1
        · apply scopedEquiv.right_inv
        · induction blocks with
          | nil => rfl
          | cons pair rest ih =>
              simp only [List.map_cons]
              have hp := scopedEquiv.right_inv pair.2
              change scopedEquiv (scopedEquiv.symm pair.2) = pair.2 at hp
              rw [hp, ih]

end LocallyNameless.ToDeBruijn

namespace Named.FromDensem

def value : Densem.Value ν → Named.Value ν
  | .var x => .var x
  | .pair l r => .pair (value l) (value r)
  | .unit => .unit

def operand : Densem.Operand φ ν → Named.Operand ν φ
  | .value v => .value (value v)
  | .op f v => .op f (value v)
  | .inl v => .inl (value v)
  | .inr v => .inr (value v)
  | .abort v => .abort (value v)

def terminator : Densem.Terminator φ ν κ → Named.Terminator ν φ κ
  | .br label => .br label
  | .ret v => .ret (value v)
  | .ite discr l r => .ite (operand discr) (terminator l) (terminator r)

/-- Existing named densem syntax embeds by retaining every destination name. -/
def block : Densem.Block φ ν κ → Named.Block ν φ κ
  | .terminator term => .terminator (terminator term)
  | .let₁ dst rhs rest => .let₁ (some dst) (operand rhs) (block rest)
  | .let₂ fst snd rhs rest => .let₂ (some fst) (some snd) (operand rhs) (block rest)

def cfg (g : Densem.CFG φ ν κ) : Named.CFG ν φ κ where
  entry := block g.entry
  blocks := g.blocks.map fun pair => (pair.1, block pair.2)

end Named.FromDensem

namespace Named.ToDensem

def value : Named.Value ν → Densem.Value ν
  | .var x => .var x
  | .pair l r => .pair (value l) (value r)
  | .unit => .unit

def operand : Named.Operand ν φ → Densem.Operand φ ν
  | .value v => .value (value v)
  | .op f v => .op f (value v)
  | .inl v => .inl (value v)
  | .inr v => .inr (value v)
  | .abort v => .abort (value v)

def terminator : Named.Terminator ν φ κ → Densem.Terminator φ ν κ
  | .br label => .br label
  | .ret v => .ret (value v)
  | .ite discr l r => .ite (operand discr) (terminator l) (terminator r)

/-- Erasing binder annotations is defined precisely for fully named blocks. -/
def block : Named.Block ν φ κ → Option (Densem.Block φ ν κ)
  | .terminator term => some (.terminator (terminator term))
  | .let₁ (some dst) rhs rest =>
      (block rest).map fun tail => .let₁ dst (operand rhs) tail
  | .let₁ none _ _ => none
  | .let₂ (some fst) (some snd) rhs rest =>
      (block rest).map fun tail => .let₂ fst snd (operand rhs) tail
  | .let₂ _ _ _ _ => none

def cfg (g : Named.CFG ν φ κ) : Option (Densem.CFG φ ν κ) :=
  (block g.entry).bind fun entry =>
    (g.blocks.mapM fun pair =>
      (block pair.2).bind fun out => some (pair.1, out)).bind fun blocks =>
        some { entry, blocks }

@[simp] theorem value_fromDensem (v : Densem.Value ν) :
    value (Named.FromDensem.value v) = v := by
  induction v <;> simp [value, Named.FromDensem.value, *]

@[simp] theorem operand_fromDensem (o : Densem.Operand φ ν) :
    operand (Named.FromDensem.operand o) = o := by
  cases o <;> simp [operand, Named.FromDensem.operand]

@[simp] theorem terminator_fromDensem (t : Densem.Terminator φ ν κ) :
    terminator (Named.FromDensem.terminator t) = t := by
  induction t <;> simp [terminator, Named.FromDensem.terminator, *]

/-- Fully named densem TAC is a retract of binder-aware named lambda-TAC. -/
@[simp] theorem block_fromDensem (b : Densem.Block φ ν κ) :
    block (Named.FromDensem.block b) = some b := by
  induction b <;> simp [block, Named.FromDensem.block, *]

/-- Being fully named is intrinsic: it means that erasure succeeds. -/
def FullyNamed (b : Named.Block ν φ κ) : Prop := ∃ out, block b = some out

theorem fullyNamed_fromDensem (b : Densem.Block φ ν κ) :
    FullyNamed (Named.FromDensem.block b) := ⟨b, block_fromDensem b⟩

theorem blocks_fromDensem (blocks : List (κ × Densem.Block φ ν κ)) :
    List.mapM (fun pair : κ × Named.Block ν φ κ =>
        (block pair.2).bind fun out => some (pair.1, out))
      (blocks.map fun pair => (pair.1, Named.FromDensem.block pair.2)) =
      some blocks := by
  induction blocks with
  | nil => rfl
  | cons pair rest ih =>
      simp only [List.map_cons, List.mapM_cons, block_fromDensem]
      simp only [Option.bind_some]
      rw [ih]
      rfl

@[simp] theorem cfg_fromDensem (g : Densem.CFG φ ν κ) :
    cfg (Named.FromDensem.cfg g) = some g := by
  cases g with
  | mk entry blocks =>
      simp only [Named.FromDensem.cfg, cfg, block_fromDensem, Option.bind_some]
      rw [blocks_fromDensem]
      rfl

/-- Whole-CFG complete-Elgot semantics commutes on the embedded existing
named-variable presentation. -/
theorem denote_fromDensem [Monad m] [Isotope.Elgot.Iterate m]
    [DecidableEq ν] [DecidableEq κ]
    (M : Densem.Monadic.Model φ m) (g : Densem.CFG φ ν κ)
    (ρ : Densem.Monadic.Env M ν) :
    (cfg (Named.FromDensem.cfg g)).map
        (fun out => Densem.Monadic.CFG.denote M out ρ) =
      some (Densem.Monadic.CFG.denote M g ρ) := by
  rw [cfg_fromDensem]
  rfl

def FullyNamedCFG (g : Named.CFG ν φ κ) : Prop := ∃ out, cfg g = some out

theorem fullyNamedCFG_fromDensem (g : Densem.CFG φ ν κ) :
    FullyNamedCFG (Named.FromDensem.cfg g) := ⟨g, cfg_fromDensem g⟩

end Named.ToDensem

end Isotope.TAC.Bridge.Lambda3AddrNamedLN
