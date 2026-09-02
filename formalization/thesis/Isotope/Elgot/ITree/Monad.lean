import Isotope.Elgot.ITree.Basic

/-!
# The monad structure on weak interaction trees

Sequencing is defined depth by depth: `Approx.bind` grafts the continuation onto
every return of a finite observation, charging one unit of depth at each visible
event.  `Approx.truncate_bind` is the coherence square that lifts this to trees,
and the monad laws are then proved observation-wise.
-/

namespace Isotope.Elgot.ITree

universe u

namespace Approx

/-- Bind finite observations, consuming one unit of depth at every visible event. -/
def bind {E : Type u → Type u} {A B : Type (u + 1)} :
    (n : Nat) → Approx E A n → (A → Approx E B n) → Approx E B n
  | 0, _, _ => PUnit.unit
  | n + 1, x, k => x >>= fun
      | .ret a => k a
      | .vis e next => Part.some (.vis e (fun r => bind n (next r)
          (fun a => truncate n (k a))))

/-- Depth-zero sequencing carries no information. -/
@[simp] theorem bind_zero {E : Type u → Type u} {A B : Type (u + 1)}
    (x : Approx E A 0) (k : A → Approx E B 0) : bind 0 x k = PUnit.unit := rfl

/-- Truncation commutes with sequencing of finite observations. -/
theorem truncate_bind {E : Type u → Type u} {A B : Type (u + 1)}
    (n : Nat) (x : Approx E A (n + 1)) (k : A → Approx E B (n + 1)) :
    truncate n (bind (n + 1) x k) =
      bind n (truncate n x) (fun a => truncate n (k a)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [truncate, bind, Part.map_eq_map, Part.bind_eq_bind, Part.map_bind,
        Part.bind_map]
      apply congrArg (Part.bind x)
      funext node
      cases node with
      | ret a => simp
      | vis e next =>
          simp
          congr
          funext r
          change truncate n (bind (n + 1) (next r) (fun a => truncate (n + 1) (k a))) = _
          exact ih (next r) (fun a => truncate (n + 1) (k a))

end Approx

/-- Monadic sequencing of weak interaction trees. -/
def bind {E : Type u → Type u} {A B : Type (u + 1)}
    (t : Tree E A) (k : A → Tree E B) : Tree E B where
  observe n := Approx.bind n (t.observe n) (fun a => (k a).observe n)
  coherent n := by
    rw [Approx.truncate_bind]
    congr 1
    · exact t.coherent n
    · funext a
      exact (k a).coherent n

/-- Weak interaction trees form a monad: `pure` is `ret`, `bind` is `bind`. -/
instance instMonad (E : Type u → Type u) : Monad (Tree E) where
  pure := ret
  bind := bind

/-- The observations of `pure`. -/
@[simp] theorem observe_pure {E : Type u → Type u} {A : Type (u + 1)} (a : A) (n : Nat) :
    (pure a : Tree E A).observe n = match n with
      | 0 => PUnit.unit
      | _ + 1 => Part.some (.ret a) := by
  cases n <;> rfl

/-- The observations of a sequencing. -/
@[simp] theorem observe_bind {E : Type u → Type u} {A B : Type (u + 1)}
    (t : Tree E A) (k : A → Tree E B) (n : Nat) :
    (t >>= k).observe n = Approx.bind n (t.observe n) (fun a => (k a).observe n) := rfl

namespace Approx

/-- The left unit law at a fixed observation depth. -/
theorem pure_bind {E : Type u → Type u} {A B : Type (u + 1)}
    (n : Nat) (a : A) (k : A → Approx E B n) :
    bind n ((ret (E := E) a).observe n) k = k a := by
  cases n with
  | zero => cases k a; rfl
  | succ => simp [bind, ret]

/-- The right unit law at a fixed observation depth. -/
theorem bind_pure {E : Type u → Type u} {A : Type (u + 1)}
    (n : Nat) (x : Approx E A n) :
    bind n x (fun a => (ret (E := E) a).observe n) = x := by
  induction n with
  | zero => cases x; rfl
  | succ n ih =>
      change x >>= (fun node => match node with
        | .ret a => (ret (E := E) a).observe (n + 1)
        | .vis e next => Part.some (.vis e (fun r =>
            bind n (next r) (fun a => truncate n ((ret (E := E) a).observe (n + 1)))))) = x
      calc
        _ = x >>= pure := by
          apply congrArg (x >>= ·)
          funext node
          cases node with
          | ret => rfl
          | vis e next =>
              simp [ret, truncate, Part.map_eq_map]
              congr
              funext r
              have hret (a : A) : truncate n (Part.some (.ret a)) =
                  (ret (E := E) a).observe n := (ret (E := E) a).coherent n
              simp_rw [hret]
              exact ih (next r)
        _ = x := _root_.bind_pure x

/-- Associativity at a fixed observation depth. -/
theorem bind_assoc {E : Type u → Type u} {A B C : Type (u + 1)}
    (n : Nat) (x : Approx E A n) (f : A → Approx E B n) (g : B → Approx E C n) :
    bind n (bind n x f) g = bind n x (fun a => bind n (f a) g) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [bind, LawfulMonad.bind_assoc]
      apply congrArg (x >>= ·)
      funext node
      cases node with
      | ret a => rfl
      | vis e next =>
          simp
          congr
          funext r
          rw [ih]
          congr
          funext a
          exact (truncate_bind n (f a) g).symm

end Approx

/-- The monad laws hold on the nose for weak interaction trees. -/
instance instLawfulMonad (E : Type u → Type u) : LawfulMonad (Tree E) :=
  LawfulMonad.mk'
    (id_map := fun t => by
      apply Tree.ext
      intro n
      change Approx.bind n (t.observe n) (fun a => (ret a).observe n) = t.observe n
      exact Approx.bind_pure n (t.observe n))
    (pure_bind := fun a f => by
      apply Tree.ext
      intro n
      exact Approx.pure_bind n a (fun x => (f x).observe n))
    (bind_assoc := fun t f g => by
      apply Tree.ext
      intro n
      exact Approx.bind_assoc n (t.observe n) (fun a => (f a).observe n)
        (fun b => (g b).observe n))
    (bind_pure_comp := fun f t => by
      apply Tree.ext
      intro n
      change Approx.bind n (t.observe n) (fun a => (ret (f a)).observe n) = _
      rfl)

end Isotope.Elgot.ITree
