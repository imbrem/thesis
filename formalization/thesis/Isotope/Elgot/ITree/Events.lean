import Isotope.Elgot.ITree.Handlers

/-!
# Event signatures: sums, injections, and subevents

Handlers only compose if signatures do.  `Sum1 E F` is the coproduct of two
event signatures, `Sum1.case1` its eliminator, and `Subevent E F` the class of
signature inclusions, so that `Subevent.trigger` can raise a single event into
any larger signature without naming the injection.

Everything here is type-level plumbing over `translate`; the content is in the
computation lemmas relating `translate` to the injections and to `case1`.
-/

namespace Isotope.Elgot.ITree

universe u

variable {E F G : Type u → Type u} {A : Type (u + 1)}

/-! ## The coproduct of two signatures -/

/-- The coproduct of two event signatures. -/
inductive Sum1 (E F : Type u → Type u) (R : Type u) : Type u
  | inl (event : E R)
  | inr (event : F R)

/-- Inject on the left of a signature coproduct. -/
def Sum1.inl1 (E F : Type u → Type u) : ∀ R : Type u, E R → Sum1 E F R :=
  fun _ e => .inl e

/-- Inject on the right of a signature coproduct. -/
def Sum1.inr1 (E F : Type u → Type u) : ∀ R : Type u, F R → Sum1 E F R :=
  fun _ e => .inr e

/-- Eliminate a signature coproduct. -/
def Sum1.case1 (g : ∀ R : Type u, E R → G R) (h : ∀ R : Type u, F R → G R) :
    ∀ R : Type u, Sum1 E F R → G R
  | _, .inl e => g _ e
  | _, .inr e => h _ e

/-- `case1` on a left injection. -/
@[simp] theorem Sum1.case1_inl1 (g : ∀ R : Type u, E R → G R) (h : ∀ R : Type u, F R → G R)
    (R : Type u) (e : E R) : Sum1.case1 g h R (Sum1.inl1 E F R e) = g R e := rfl

/-- `case1` on a right injection. -/
@[simp] theorem Sum1.case1_inr1 (g : ∀ R : Type u, E R → G R) (h : ∀ R : Type u, F R → G R)
    (R : Type u) (e : F R) : Sum1.case1 g h R (Sum1.inr1 E F R e) = h R e := rfl

/-- `case1` of the two injections is the identity. -/
@[simp] theorem Sum1.case1_inl1_inr1 :
    Sum1.case1 (Sum1.inl1 E F) (Sum1.inr1 E F) = fun _ e => e := by
  funext R e; cases e <;> rfl

/-! ## Subevents -/

/-- `E` is a subsignature of `F`: every `E`-event names an `F`-event. -/
class Subevent (E F : Type u → Type u) where
  /-- The inclusion of `E`-events into `F`-events. -/
  inject : ∀ R : Type u, E R → F R

/-- Every signature includes into itself. -/
instance (priority := 100) Subevent.instRefl : Subevent E E := ⟨fun _ e => e⟩

/-- The left summand includes into a signature coproduct. -/
instance Subevent.instInl : Subevent E (Sum1 E F) := ⟨Sum1.inl1 E F⟩

/-- The right summand includes into a signature coproduct. -/
instance Subevent.instInr : Subevent F (Sum1 E F) := ⟨Sum1.inr1 E F⟩

/-- Raise a tree into a larger signature. -/
def send [Subevent E F] (t : Tree E A) : Tree F A := translate Subevent.inject t

/-- A single visible event of a subsignature, returning its response. -/
def Subevent.trigger [Subevent E F] {R : Type u} (e : E R) : Tree F (ULift.{u + 1} R) :=
  vis (Subevent.inject R e) (fun r => ret (ULift.up r))

/-- `Subevent.trigger` at the trivial inclusion is `trigger`. -/
@[simp] theorem Subevent.trigger_self {R : Type u} (e : E R) :
    Subevent.trigger (F := E) e = trigger e := rfl

/-- Raising along the trivial inclusion does nothing. -/
@[simp] theorem send_self (t : Tree E A) : send (F := E) t = t := translate_id t

/-- Raising a tree is relabelling, so it preserves returns. -/
@[simp] theorem send_ret [Subevent E F] (a : A) : send (E := E) (F := F) (ret a) = ret a :=
  translate_ret _ a

/-- Raising a tree preserves divergence. -/
@[simp] theorem send_diverge [Subevent E F] :
    send (E := E) (F := F) (diverge : Tree E A) = diverge := translate_diverge _

/-- Raising a tree injects its events. -/
@[simp] theorem send_vis [Subevent E F] {R : Type u} (e : E R) (k : R → Tree E A) :
    send (F := F) (vis e k) = vis (Subevent.inject R e) (fun r => send (F := F) (k r)) :=
  translate_vis _ e k

/-- Raising commutes with sequencing. -/
theorem send_bind [Subevent E F] {B : Type (u + 1)} (t : Tree E A) (k : A → Tree E B) :
    send (F := F) (t >>= k) = send (F := F) t >>= fun a => send (F := F) (k a) :=
  translate_bind _ t k

/-! ## Interpreting one summand at a time -/

/-- Relabelling into a coproduct and then eliminating recovers the left handler. -/
@[simp] theorem translate_case1_inl1 (g : ∀ R : Type u, E R → G R)
    (h : ∀ R : Type u, F R → G R) (t : Tree E A) :
    translate (Sum1.case1 g h) (translate (Sum1.inl1 E F) t) = translate g t :=
  translate_translate _ _ t

/-- Relabelling into a coproduct and then eliminating recovers the right handler. -/
@[simp] theorem translate_case1_inr1 (g : ∀ R : Type u, E R → G R)
    (h : ∀ R : Type u, F R → G R) (t : Tree F A) :
    translate (Sum1.case1 g h) (translate (Sum1.inr1 E F) t) = translate h t :=
  translate_translate _ _ t

/-- Eliminating a coproduct of injections is the identity. -/
@[simp] theorem translate_case1_id (t : Tree (Sum1 E F) A) :
    translate (Sum1.case1 (Sum1.inl1 E F) (Sum1.inr1 E F)) t = t := by
  rw [Sum1.case1_inl1_inr1]; exact translate_id t

end Isotope.Elgot.ITree
