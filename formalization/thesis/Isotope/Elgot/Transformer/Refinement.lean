import Isotope.Elgot.StateT
import Isotope.Elgot.Brookes.SeqCst
import Isotope.Elgot.Brookes.Iteration

/-! # Refinement lifted through state transformers -/

namespace Isotope.Elgot.Transformer

universe u

/-- Order-theoretic laws needed to transport refinement through a monad.
The relation is explicit, so this does not compete with global `LE` instances
on concrete semantic monads. -/
structure MonadOrder (m : Type u → Type u) [Monad m] where
  le : {A : Type u} → m A → m A → Prop
  refl : ∀ {A} (x : m A), le x x
  trans : ∀ {A} {x y z : m A}, le x y → le y z → le x z
  antisymm : ∀ {A} {x y : m A}, le x y → le y x → x = y
  bind_mono : ∀ {A B} {x y : m A} {f g : A → m B},
    le x y → (∀ a, le (f a) (g a)) → le (x >>= f) (y >>= g)

/-- An ordered monad whose Elgot iteration operator is monotone. -/
structure LawfulElgotOrder (m : Type u → Type u) [Monad m] [Iterate m]
    extends MonadOrder m where
  iter_mono : ∀ {A B} {f g : A → m (B ⊕ A)},
    (∀ a, toMonadOrder.le (f a) (g a)) →
      ∀ a, toMonadOrder.le (iter f a) (iter g a)

namespace StateT

variable {m : Type u → Type u} [Monad m]

/-- State-transformer refinement is pointwise refinement in the base monad. -/
def Refines (O : MonadOrder m) {S A : Type u}
    (f g : _root_.StateT S m A) : Prop := ∀ s, O.le (f s) (g s)

theorem refines_refl (O : MonadOrder m) {S A : Type u}
    (f : _root_.StateT S m A) : Refines O f f := fun s => O.refl (f s)

theorem refines_trans (O : MonadOrder m) {S A : Type u}
    {f g h : _root_.StateT S m A} (hfg : Refines O f g)
    (hgh : Refines O g h) : Refines O f h := fun s => O.trans (hfg s) (hgh s)

theorem refines_antisymm (O : MonadOrder m) {S A : Type u}
    {f g : _root_.StateT S m A} (hfg : Refines O f g)
    (hgf : Refines O g f) : f = g := by
  funext s
  exact O.antisymm (hfg s) (hgf s)

theorem pure_refines (O : MonadOrder m) {S A : Type u} (a : A) :
    Refines O (pure a : _root_.StateT S m A) (pure a) := refines_refl O _

/-- StateT bind is monotone whenever base bind is monotone. -/
theorem bind_refines (O : MonadOrder m) {S A B : Type u}
    {x y : _root_.StateT S m A} {f g : A → _root_.StateT S m B}
    (hxy : Refines O x y) (hfg : ∀ a, Refines O (f a) (g a)) :
    Refines O (x >>= f) (y >>= g) := by
  intro s
  exact O.bind_mono (hxy s) fun p => hfg p.1 p.2

/-- The pointwise order on `StateT S m` induced by a base monad order. -/
def liftOrder (O : MonadOrder m) (S : Type u) : MonadOrder (_root_.StateT S m) where
  le := Refines O
  refl := refines_refl O
  trans := refines_trans O
  antisymm := refines_antisymm O
  bind_mono := bind_refines O

/-- StateT preserves monotonicity of Elgot iteration. -/
def liftElgotOrder [Iterate m] (O : LawfulElgotOrder m) (S : Type u) :
    LawfulElgotOrder (_root_.StateT S m) where
  toMonadOrder := liftOrder O.toMonadOrder S
  iter_mono := by
    intro A B f g h a s
    exact O.iter_mono (fun p =>
      O.toMonadOrder.bind_mono (h p.1 p.2) fun _ => O.toMonadOrder.refl _) (a, s)

end StateT

namespace Brookes

theorem approx_mono {E A B : Type u} {c : Isotope.Elgot.Brookes.Rewriting E}
    {f g : A → Isotope.Elgot.Brookes c (B ⊕ A)}
    (h : ∀ a, f a ≤ g a) (n : Nat) (a : A) :
    Isotope.Elgot.Brookes.approx f n a ≤ Isotope.Elgot.Brookes.approx g n a := by
  induction n generalizing a with
  | zero => exact bot_le
  | succ n ih =>
      exact Isotope.Elgot.Brookes.bind_mono (h a) fun
        | .inl _ => le_rfl
        | .inr a' => ih a'

theorem iter_mono {E A B : Type u} {c : Isotope.Elgot.Brookes.Rewriting E}
    {f g : A → Isotope.Elgot.Brookes c (B ⊕ A)}
    (h : ∀ a, f a ≤ g a) (a : A) : iter f a ≤ iter g a := by
  apply Isotope.Elgot.Brookes.iter_le f a
  intro n
  exact le_trans (approx_mono h n a)
    (Isotope.Elgot.Brookes.approx_le_iter g n a)

/-- Inclusion refinement makes every Brookes monad an ordered monad. -/
def monadOrder {E : Type u} (c : Isotope.Elgot.Brookes.Rewriting E) :
    MonadOrder (Isotope.Elgot.Brookes c) where
  le := (· ≤ ·)
  refl := fun _ => le_rfl
  trans := fun h k => le_trans h k
  antisymm := fun h k => le_antisymm h k
  bind_mono := Isotope.Elgot.Brookes.bind_mono

def lawfulElgotOrder {E : Type u} (c : Isotope.Elgot.Brookes.Rewriting E) :
    LawfulElgotOrder (Isotope.Elgot.Brookes c) where
  toMonadOrder := monadOrder c
  iter_mono := iter_mono

/-- The concrete sequentially-consistent Brookes memory model carries the
refinement order required by the transformer lifting interface. -/
def seqCstMonadOrder (Loc Val : Type u) :
    MonadOrder (Isotope.Elgot.Brookes.SeqCst.Comp Loc Val) :=
  monadOrder (Isotope.Elgot.Brookes.SeqCst.rewriting
    (Isotope.Elgot.Brookes.SeqCst.Store Loc Val))

def seqCstLawfulElgotOrder (Loc Val : Type u) :
    LawfulElgotOrder (Isotope.Elgot.Brookes.SeqCst.Comp Loc Val) :=
  lawfulElgotOrder (Isotope.Elgot.Brookes.SeqCst.rewriting
    (Isotope.Elgot.Brookes.SeqCst.Store Loc Val))

/-- Adding a private state component to the sequentially-consistent memory
model preserves its refinement structure pointwise. -/
def seqCstStateOrder (Private Loc Val : Type u) :
    MonadOrder (_root_.StateT.{u, u} Private
      (Isotope.Elgot.Brookes.SeqCst.Comp Loc Val)) :=
  StateT.liftOrder (seqCstMonadOrder Loc Val) Private

def seqCstStateLawfulElgotOrder (Private Loc Val : Type u) :
    LawfulElgotOrder (_root_.StateT.{u, u} Private
      (Isotope.Elgot.Brookes.SeqCst.Comp Loc Val)) :=
  StateT.liftElgotOrder (seqCstLawfulElgotOrder Loc Val) Private

end Brookes
end Isotope.Elgot.Transformer
