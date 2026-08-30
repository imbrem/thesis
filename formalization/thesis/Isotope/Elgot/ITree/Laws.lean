import Isotope.Elgot.ITree.Iteration

namespace Isotope.Elgot.ITree

open Isotope.Elgot

universe u

namespace Approx

theorem iter_fixpoint {E : Type u → Type u} {A B : Type (u + 1)}
    (n : Nat) (x : Approx E (B ⊕ A) n) (f : A → Approx E (B ⊕ A) n) :
    iter n x f = bind n x (Sum.elim
      (fun b => (ret (E := E) b).observe n)
      (fun a => iter n (f a) f)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [iter_succ, LawfulElgotMonad.fixpoint]
      simp only [iterStep, bind, LawfulMonad.bind_assoc]
      apply congrArg (x >>= ·)
      funext node
      cases node with
      | ret s =>
          cases s <;> simp [ret]
      | vis e next =>
          simp
          congr
          funext r
          rw [ih (next r) (fun a => truncate n (f a))]
          apply congrArg (bind n (next r))
          funext s
          cases s with
          | inl b => exact ((ret (E := E) b).coherent n).symm
          | inr a => exact (truncate_iter n (f a) f).symm

/-- Act effectfully on the returned summand of a finite observation. -/
def mapReturn {E : Type u → Type u} {A B C : Type (u + 1)} (n : Nat)
    (x : Approx E (B ⊕ A) n) (g : B → Approx E C n) : Approx E (C ⊕ A) n :=
  bind n x (Sum.elim
    (fun b => bind n (g b) (fun c => (ret (E := E) (Sum.inl c)).observe n))
    (fun a => (ret (E := E) (Sum.inr a)).observe n))

/-- Residual-state simulation: effectful return mapping commutes with forgetting
the deepest visible observation. -/
theorem truncate_mapReturn {E : Type u → Type u} {A B C : Type (u + 1)}
    (n : Nat) (x : Approx E (B ⊕ A) (n + 1)) (g : B → Approx E C (n + 1)) :
    truncate n (mapReturn (n + 1) x g) =
      mapReturn n (truncate n x) (fun b => truncate n (g b)) := by
  rw [mapReturn, truncate_bind]
  unfold mapReturn
  apply congrArg (bind n (truncate n x))
  funext s
  cases s with
  | inl b =>
      simp only [Sum.elim_inl]
      rw [truncate_bind]
      apply congrArg (bind n (truncate n (g b)))
      funext c
      exact (ret (E := E) (Sum.inl c)).coherent n
  | inr a =>
      simp only [Sum.elim_inr]
      exact (ret (E := E) (Sum.inr a)).coherent n

def mapInl {E : Type u → Type u} {A B : Type (u + 1)} (n : Nat)
    (x : Approx E B n) : Approx E (B ⊕ A) n :=
  bind n x (fun b => (ret (E := E) (Sum.inl b)).observe n)

theorem truncate_mapInl {E : Type u → Type u} {A B : Type (u + 1)}
    (n : Nat) (x : Approx E B (n + 1)) :
    truncate n (mapInl (A := A) (n + 1) x) = mapInl n (truncate n x) := by
  rw [mapInl, truncate_bind]
  unfold mapInl
  apply congrArg (bind n (truncate n x))
  funext b
  exact (ret (E := E) (Sum.inl b)).coherent n

theorem iter_mapInl {E : Type u → Type u} {A B : Type (u + 1)}
    (n : Nat) (x : Approx E B n) (f : A → Approx E (B ⊕ A) n) :
    iter n (mapInl n x) f = x := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [iter_succ, LawfulElgotMonad.fixpoint]
      simp only [mapInl, bind, iterStep, LawfulMonad.bind_assoc]
      calc
        _ = x >>= pure := by
          apply congrArg (x >>= ·)
          funext node
          cases node with
          | ret b => simp [ret]
          | vis e next =>
              simp
              congr
              funext r
              rw [show (fun b => truncate n ((ret (E := E) (Sum.inl b)).observe (n + 1))) =
                  (fun b => (ret (E := E) (Sum.inl b)).observe n) by
                funext b
                exact (ret (E := E) (Sum.inl b)).coherent n]
              exact ih (next r) (fun a => truncate n (f a))
        _ = x := by
          change Part.bind x Part.some = x
          rw [Part.bind_some_eq_map]
          exact Part.map_id' (fun _ => rfl) x

def post {E : Type u → Type u} {B C : Type (u + 1)} (n : Nat)
    (g : B → Approx E C (n + 1)) :
    Visible E B (Approx E B n) → Part (Visible E C (Approx E C n))
  | .ret b => g b
  | .vis e next => Part.some (.vis e (fun r => bind n (next r)
      (fun b => truncate n (g b))))

private theorem naturality_square {E : Type u → Type u} {A B C : Type (u + 1)}
    (n : Nat) (f : A → Approx E (B ⊕ A) (n + 1))
    (g : B → Approx E C (n + 1))
    (ih : ∀ x, bind n (iter n x (fun a => truncate n (f a)))
        (fun b => truncate n (g b)) =
      iter n (mapReturn (A := A) n x (fun b => truncate n (g b)))
        (fun a => mapReturn (A := A) n (truncate n (f a)) (fun b => truncate n (g b)))) :
    kcomp (Isotope.Elgot.mapReturn (iterStep n f) (post n g))
        (liftPure (Sum.map
          (id : Visible E C (Approx E C n) → Visible E C (Approx E C n))
          (fun x => mapReturn (A := A) (B := B) (C := C) (n + 1) x g))) =
      kcomp (liftPure (fun x => mapReturn (A := A) (B := B) (C := C) (n + 1) x g))
        (iterStep n (fun a => mapReturn (A := A) (B := B) (C := C) (n + 1) (f a) g)) := by
  funext x
  simp only [kcomp, Isotope.Elgot.mapReturn, liftPure, Function.comp_apply, iterStep,
    post, mapReturn, bind, LawfulMonad.bind_assoc]
  simp only [Part.pure_eq_some, Part.bind_eq_bind, Part.bind_some]
  simp only [iterStep]
  simp only [Part.bind_eq_bind]
  rw [Part.bind_assoc]
  apply congrArg (Part.bind x)
  funext node
  cases node with
  | ret s =>
      cases s with
      | inl b =>
          simp [Part.bind_assoc]
          apply congrArg (Part.bind (g b))
          funext node
          cases node with
          | ret c => simp [ret, iterStep]
          | vis e next =>
              simp
              congr
              funext r
              rw [show (fun c => truncate n ((ret (E := E) (Sum.inl c)).observe (n + 1))) =
                  (fun c => (ret (E := E) (Sum.inl c)).observe n) by
                funext c
                exact (ret (E := E) (Sum.inl c)).coherent n]
              exact (iter_mapInl n (next r) _).symm
      | inr a => simp [ret, iterStep]
  | vis e next =>
      simp
      congr
      funext r
      calc
        _ = iter n (mapReturn (A := A) (B := B) (C := C) n (next r)
              (fun b => truncate n (g b)))
            (fun a => mapReturn (A := A) (B := B) (C := C) n (truncate n (f a))
              (fun b => truncate n (g b))) := ih (next r)
        _ = _ := by
          congr 1
          · unfold mapReturn
            apply congrArg (bind n (next r))
            funext s
            cases s with
            | inl b =>
                simp only [Sum.elim_inl]
                exact (truncate_mapInl (A := A) n (g b)).symm
            | inr a =>
                simp only [Sum.elim_inr]
                exact ((ret (E := E) (Sum.inr a : C ⊕ A)).coherent n).symm
          · funext a
            exact (truncate_mapReturn (A := A) n (f a) g).symm

theorem iter_naturality {E : Type u → Type u} {A B C : Type (u + 1)}
    (n : Nat) (x : Approx E (B ⊕ A) n) (f : A → Approx E (B ⊕ A) n)
    (g : B → Approx E C n) :
    bind n (iter n x f) g =
      iter n (mapReturn (A := A) n x g) (fun a => mapReturn (A := A) n (f a) g) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change kcomp (Isotope.Elgot.iter (iterStep n f)) (post n g) x = _
      rw [LawfulElgotMonad.naturality]
      rw [LawfulElgotMonad.uniformity
        (Isotope.Elgot.mapReturn (iterStep n f) (post n g))
        (iterStep n (fun a => mapReturn (A := A) (n + 1) (f a) g))
        (fun x => mapReturn (A := A) (n + 1) x g)
        (naturality_square n f g (fun y => ih y (fun a => truncate n (f a))
          (fun b => truncate n (g b))))]
      simp [kcomp, liftPure]

/-- Rename only the recursive return summand of a finite observation. -/
def mapState {E : Type u → Type u} {A B C : Type (u + 1)} (n : Nat)
    (x : Approx E (B ⊕ A) n) (h : A → C) : Approx E (B ⊕ C) n :=
  bind n x (fun s => (ret (E := E) (Sum.map id h s)).observe n)

theorem truncate_mapState {E : Type u → Type u} {A B C : Type (u + 1)}
    (n : Nat) (x : Approx E (B ⊕ A) (n + 1)) (h : A → C) :
    truncate n (mapState (n + 1) x h) = mapState n (truncate n x) h := by
  rw [mapState, truncate_bind]
  unfold mapState
  apply congrArg (bind n (truncate n x))
  funext s
  exact (ret (E := E) (Sum.map id h s)).coherent n

private theorem uniformity_square {E : Type u → Type u} {A B C : Type (u + 1)}
    (n : Nat) (f : A → Approx E (B ⊕ A) (n + 1))
    (g : C → Approx E (B ⊕ C) (n + 1)) (h : A → C)
    (comm : ∀ a, mapState (n + 1) (f a) h = g (h a))
    (ih : ∀ x, iter n x (fun a => truncate n (f a)) =
      iter n (mapState n x h) (fun c => truncate n (g c))) :
    kcomp (iterStep n f)
        (liftPure (Sum.map id (fun x => mapState (n + 1) x h))) =
      kcomp (liftPure (fun x => mapState (n + 1) x h)) (iterStep n g) := by
  funext x
  simp only [kcomp, liftPure, Function.comp_apply, iterStep, mapState, bind,
    LawfulMonad.bind_assoc]
  simp only [Part.pure_eq_some, Part.bind_eq_bind, Part.bind_some]
  simp only [iterStep, Part.bind_eq_bind]
  rw [Part.bind_assoc]
  apply congrArg (Part.bind x)
  funext node
  cases node with
  | ret s =>
      cases s with
      | inl b => simp [ret, iterStep]
      | inr a =>
          simp [ret, iterStep]
          exact comm a
  | vis e next =>
      simp
      congr
      funext r
      calc
        _ = iter n (mapState n (next r) h) (fun c => truncate n (g c)) := ih (next r)
        _ = _ := by
          congr 1
          unfold mapState
          apply congrArg (bind n (next r))
          funext s
          exact ((ret (E := E) (Sum.map id h s)).coherent n).symm

theorem iter_uniformity {E : Type u → Type u} {A B C : Type (u + 1)}
    (n : Nat) (x : Approx E (B ⊕ A) n)
    (f : A → Approx E (B ⊕ A) n) (g : C → Approx E (B ⊕ C) n)
    (h : A → C) (comm : ∀ a, mapState n (f a) h = g (h a)) :
    iter n x f = iter n (mapState n x h) g := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hc (a : A) : mapState n (truncate n (f a)) h = truncate n (g (h a)) := by
        rw [← truncate_mapState]
        exact congrArg (truncate n) (comm a)
      have hs := LawfulElgotMonad.uniformity (m := Part)
        (iterStep n f) (iterStep n g) (fun x => mapState (n + 1) x h)
        (uniformity_square n f g h comm (fun y => ih y
          (fun a => truncate n (f a)) (fun c => truncate n (g c)) hc))
      change Isotope.Elgot.iter (iterStep n f) x = _
      rw [congrFun hs x]
      simp [kcomp, liftPure]

/-- Merge the two recursive summands of a finite observation. -/
def flattenApprox {E : Type u → Type u} {A B : Type (u + 1)} (n : Nat)
    (x : Approx E ((B ⊕ A) ⊕ A) n) : Approx E (B ⊕ A) n :=
  bind n x (fun s => (ret (E := E) (Isotope.Elgot.flatten s)).observe n)

theorem truncate_flattenApprox {E : Type u → Type u} {A B : Type (u + 1)}
    (n : Nat) (x : Approx E ((B ⊕ A) ⊕ A) (n + 1)) :
    truncate n (flattenApprox (n + 1) x) = flattenApprox n (truncate n x) := by
  rw [flattenApprox, truncate_bind]
  unfold flattenApprox
  apply congrArg (bind n (truncate n x))
  funext s
  exact (ret (E := E) (Isotope.Elgot.flatten s)).coherent n

end Approx

/-- The defining fixpoint equation for weak interaction-tree iteration. -/
theorem iterate_fixpoint {E : Type u → Type u} {A B : Type (u + 1)}
    (f : A → Tree E (B ⊕ A)) :
    Isotope.Elgot.iter f = fun a => f a >>= Sum.elim pure (Isotope.Elgot.iter f) := by
  funext a
  apply Tree.ext
  intro n
  rw [observe_iter, observe_bind]
  rw [Approx.iter_fixpoint]
  apply congrArg (Approx.bind n ((f a).observe n))
  funext s
  cases s with
  | inl b => rfl
  | inr a => exact observe_iter f a n

theorem iterate_naturality {E : Type u → Type u} {A B C : Type (u + 1)}
    (f : A → Tree E (B ⊕ A)) (g : B → Tree E C) :
    kcomp (Isotope.Elgot.iter f) g =
      Isotope.Elgot.iter (Isotope.Elgot.mapReturn f g) := by
  funext a
  apply Tree.ext
  intro n
  change (Isotope.Elgot.iter f a >>= g).observe n = _
  rw [observe_bind, observe_iter]
  change Approx.bind n (Approx.iter n ((f a).observe n) (fun a => (f a).observe n))
      (fun b => (g b).observe n) = _
  rw [Approx.iter_naturality]
  rw [observe_iter]
  have hm (a : A) : (Isotope.Elgot.mapReturn f g a).observe n =
      Approx.mapReturn n ((f a).observe n) (fun b => (g b).observe n) := by
    change Approx.bind n ((f a).observe n)
      (fun s => (Sum.elim (fun b => g b >>= pure ∘ Sum.inl) (pure ∘ Sum.inr) s).observe n) = _
    unfold Approx.mapReturn
    apply congrArg (Approx.bind n ((f a).observe n))
    funext s
    cases s with
    | inl b => rfl
    | inr a => rfl
  simp_rw [hm]

theorem iterate_uniformity {E : Type u → Type u} {A B C : Type (u + 1)}
    (f : A → Tree E (B ⊕ A)) (g : C → Tree E (B ⊕ C)) (h : A → C)
    (comm : kcomp f (liftPure (Sum.map id h)) = kcomp (liftPure h) g) :
    Isotope.Elgot.iter f = kcomp (liftPure h) (Isotope.Elgot.iter g) := by
  funext a
  apply Tree.ext
  intro n
  rw [observe_iter]
  change Approx.iter n ((f a).observe n) (fun a => (f a).observe n) = _
  rw [Approx.iter_uniformity n ((f a).observe n) (fun a => (f a).observe n)
    (fun c => (g c).observe n) h]
  · change Approx.iter n (Approx.mapState n ((f a).observe n) h)
      (fun c => (g c).observe n) = _
    have hc := congrFun comm a
    have ho := congrArg (fun t : Tree E (B ⊕ C) => t.observe n) hc
    have hm : Approx.mapState n ((f a).observe n) h = (g (h a)).observe n := by
      simpa [kcomp, liftPure, Approx.mapState] using ho
    rw [hm]
    simp only [kcomp, liftPure, Function.comp_apply]
    rw [pure_bind]
    change _ = (Isotope.Elgot.iter g (h a)).observe n
    exact (observe_iter g (h a) n).symm
  · intro a
    have hc := congrFun comm a
    have ho := congrArg (fun t : Tree E (B ⊕ C) => t.observe n) hc
    simpa [kcomp, liftPure, Approx.mapState] using ho

end Isotope.Elgot.ITree
