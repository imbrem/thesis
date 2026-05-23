import Isotope.STm.Closed

namespace Isotope

open Args

namespace STm

universe uwit ustor

variable {Arity} [instArgs : Args Arity] {L : Lang Arity} {A A₁ A₂}

class OpSem.Val (L : Lang Arity)
  : Type _ where
  OpP : Closed L → L.Val → Prop
  OpW : Closed L → L.Val → Type uwit

structure Lang.Store (L : Lang Arity) (A : Type _) where
  GetP : A → L.Val → Prop
  GetW : A → L.Val → Type ustor

def Lang.botStore (L : Lang Arity) (A) : Store L A where
  GetP _ _ := False
  GetW _ _ := Empty

def Lang.topStore (L : Lang Arity) (A) : Store L A where
  GetP _ _ := True
  GetW _ _ := Unit

namespace Lang.Store

instance instBot : Bot (Store L A) where
  bot := botStore L A

instance instTop : Top (Store L A) where
  top := topStore L A

instance instInhabited : Inhabited (Store L A) where
  default := ⊥

structure SubP (S₁ : Store L A) (S₂ : Store L A) : Prop where
  getP_imp_getP : ∀ {a v}, S₁.GetP a v → S₂.GetP a v

theorem SubP.refl (S : Store L A) : SubP S S where
  getP_imp_getP := fun h => h

theorem SubP.trans
  {S₁ S₂ S₃ : Store L A} (h₁₂ : SubP S₁ S₂) (h₂₃ : SubP S₂ S₃)
  : SubP S₁ S₃ where
  getP_imp_getP := fun h => h₂₃.getP_imp_getP (h₁₂.getP_imp_getP h)

instance instPreorder : Preorder (Store L A) where
  le := SubP
  le_refl := SubP.refl
  le_trans _ _ _ := SubP.trans

def castSym (S : Store L A₁) (hA : A₁ = A₂) : Store L A₂ where
  GetP a v := S.GetP (hA ▸ a) v
  GetW a v := S.GetW (hA ▸ a) v

@[simp]
theorem castSym_refl (S : Store L A) : S.castSym rfl = S
  := rfl

@[simp]
theorem castSym_castSym (S : Store L A₁) {hA₁ : A₁ = A₂} {hA₂ : A₂ = A₃} :
  (S.castSym hA₁).castSym hA₂ = S.castSym (hA₁.trans hA₂)
  := by cases hA₁; cases hA₂; rfl

@[simp]
theorem castSym_bot (hA : A₁ = A₂) : (⊥ : Store L A₁).castSym hA = ⊥
  := by cases hA; rfl

@[simp]
theorem castSym_top (hA : A₁ = A₂) : (⊤ : Store L A₁).castSym hA = ⊤
  := by cases hA; rfl

def GetP.castHSym {S : Store L A₁} {a₁ : A₁} {a₂ : A₂} {v}
  (ha₁ : S.GetP a₁ v) (ha : a₁ ≍ a₂)
  : (S.castSym (by cases ha; rfl)).GetP a₂ v
  := by cases ha; exact ha₁

@[simp]
theorem GetP.castHSym_refl {S : Store L A} (ha₁ : S.GetP a v)
  : ha₁.castHSym HEq.rfl = ha₁ := rfl

@[simp]
theorem GetP.castHSym_castHSym {S : Store L A₁} {a₁ a₂ a₃ : A₁} {v}
  (ha : S.GetP a₁ v)
  (ha₁ : a₁ ≍ a₂) (ha₂ : a₂ ≍ a₃)
  : (ha.castHSym ha₁).castHSym ha₂
  = ha.castHSym (ha₁.trans ha₂)
  := rfl

def GetW.castHSym {S : Store L A₁} {a₁ : A₁} {a₂ : A₂} {v}
  (ha₁ : S.GetW a₁ v) (ha : a₁ ≍ a₂)
  : (S.castSym (by cases ha; rfl)).GetW a₂ v
  := by cases ha; exact ha₁

@[simp]
theorem GetW.castHSym_refl {S : Store L A} (ha₁ : S.GetW a v)
  : ha₁.castHSym HEq.rfl = ha₁ := rfl

@[simp]
theorem GetW.castHSym_castHSym {S : Store L A₁} {a₁ a₂ a₃ : A₁} {v}
  (ha : S.GetW a₁ v)
  (ha₁ : a₁ ≍ a₂) (ha₂ : a₂ ≍ a₃)
  : (ha.castHSym ha₁).castHSym ha₂
  = ha.castHSym (ha₁.trans ha₂)
  := by cases ha₁; cases ha₂; rfl

structure Hom (S₁ : L.Store A₁) (S₂ : L.Store A₂) where
  toFun : A₁ → A₂
  mapGetP : ∀ {a v}, S₁.GetP a v → S₂.GetP (toFun a) v
  mapGetW : ∀ {a v}, S₁.GetW a v → S₂.GetW (toFun a) v

def idHom (S : L.Store A) : Hom S S where
  toFun := _root_.id
  mapGetP := fun h => h
  mapGetW := fun w => w

def castSymHom (S : L.Store A₁) (hA : A₁ = A₂) : Hom S (S.castSym hA)
  where
  toFun a := hA ▸ a
  mapGetP h := h.castHSym (by cases hA; rfl)
  mapGetW w := w.castHSym (by cases hA; rfl)

@[simp]
theorem castSymHom_refl (S : Store L A) : S.castSymHom rfl = idHom S
  := rfl

def Hom.comp {S₁ : L.Store A₁} {S₂ : L.Store A₂} {S₃ : L.Store A₃}
  (f : Hom S₁ S₂) (g : Hom S₂ S₃) : Hom S₁ S₃ where
  toFun := g.toFun ∘ f.toFun
  mapGetP := fun h => g.mapGetP (f.mapGetP h)
  mapGetW := fun w => g.mapGetW (f.mapGetW w)

@[simp]
theorem Hom.id_comp {S₁ : L.Store A₁} {S₂ : L.Store A₂} (f : Hom S₁ S₂) :
  Hom.comp S₁.idHom f = f := rfl

@[simp]
theorem Hom.comp_id {S₁ : L.Store A₁} {S₂ : L.Store A₂} (f : Hom S₁ S₂) :
  Hom.comp f S₂.idHom = f := rfl

@[simp]
theorem Hom.comp_assoc {A₃ A₄}
  {S₁ : L.Store A₁} {S₂ : L.Store A₂} {S₃ : L.Store A₃} {S₄ : L.Store A₄}
  (f : Hom S₁ S₂) (g : Hom S₂ S₃) (h : Hom S₃ S₄) :
  Hom.comp (Hom.comp f g) h = Hom.comp f (Hom.comp g h) := rfl

def Hom.castIn
  {S₁ : L.Store A₁}
  {S₁' : L.Store A₁}
  {S₂ : L.Store A₂}
  (he₁ : S₁ = S₁') (f : Hom S₁' S₂)
  : Hom S₁ S₂
  := he₁ ▸ f

@[simp]
theorem Hom.castIn_refl {S₁ : L.Store A₁} {S₂ : L.Store A₂} (f : Hom S₁ S₂) :
  f.castIn rfl = f := rfl

@[simp]
theorem Hom.castIn_castIn
  {S₁ S₁' S₁'' : L.Store A₁} {S₂ : L.Store A₂}
  (he₁ : S₁ = S₁') (he₁' : S₁' = S₁'') (f : Hom S₁'' S₂) :
  (f.castIn he₁').castIn he₁ = f.castIn (he₁.trans he₁')
  := by cases he₁; cases he₁'; rfl

def Hom.castOut
  {S₁ : L.Store A₁}
  {S₂ : L.Store A₂}
  {S₂' : L.Store A₂}
  (f : Hom S₁ S₂) (he₂ : S₂ = S₂')
  : Hom S₁ S₂'
  := he₂ ▸ f

@[simp]
theorem Hom.castOut_refl {S₁ : L.Store A₁} {S₂ : L.Store A₂} (f : Hom S₁ S₂) :
  f.castOut rfl = f := rfl

@[simp]
theorem Hom.castOut_castOut
  {S₁ : L.Store A₁} {S₂ S₂' S₂'' : L.Store A₂}
  (he₂ : S₂ = S₂') (he₂' : S₂' = S₂'') (f : Hom S₁ S₂) :
  (f.castOut he₂).castOut he₂' = f.castOut (he₂.trans he₂')
  := by cases he₂; cases he₂'; rfl

theorem Hom.castIn_castOut
  {S₁ S₁' : L.Store A₁} {S₂ S₂' : L.Store A₂}
  (he₁ : S₁ = S₁') (he₂ : S₂ = S₂')
  (f : Hom S₁' S₂)
  : (f.castIn he₁).castOut he₂ = (f.castOut he₂).castIn he₁
  := by cases he₁; cases he₂; rfl

-- TODO: castSymHom_comp

def fromBot (toFun : A₁ → A₂) (S : L.Store A₂)
  : Hom (⊥ : L.Store A₁) S where
  toFun := toFun
  mapGetP := fun h => nomatch h
  mapGetW := fun w => nomatch w

def toTop (S : L.Store A₁) (toFun : A₁ → A₂)
  : Hom S (⊤ : L.Store A₂) where
  toFun := toFun
  mapGetP := fun _ => by trivial
  mapGetW := fun _ => ()

class LocalSound (L : Lang Arity) (S : L.Store A) where
  sound : ∀ {a} {v : L.Val}, S.GetP a v → Nonempty (S.GetW a v)

class LocalComplete (L : Lang Arity) (S : L.Store A) where
  complete : ∀ {a} {v : L.Val}, S.GetW a v → S.GetP a v

class LocalCorrect (L : Lang Arity) (S : L.Store A)
  extends LocalSound L S, LocalComplete L S

instance instBotLocalCorrect (L : Lang Arity) (A)
  : LocalCorrect L (L.botStore A) where
  sound := fun h => nomatch h
  complete := fun w => nomatch w

instance instTopLocalCorrect (L : Lang Arity) (A)
  : LocalCorrect L (L.topStore A) where
  sound := fun _ => ⟨()⟩
  complete := fun _ => by trivial

class Det (L : Lang Arity) (S : L.Store A) where
  det : ∀ {a} {v₁ v₂ : L.Val}, S.GetP a v₁ → S.GetP a v₂ → v₁ = v₂

end Lang.Store

variable [instOpSem : OpSem.Val L]

namespace OpSem.Val

class LocalSound (L : Lang Arity) [OpSem.Val L] where
  sound : ∀ {e} {v : L.Val}, OpP e v → Nonempty (OpW e v)

class LocalComplete (L : Lang Arity) [OpSem.Val L] where
  complete : ∀ {e} {v : L.Val}, OpW e v → OpP e v

class LocalCorrect (L : Lang Arity) [OpSem.Val L]
  extends LocalSound L, LocalComplete L

class Det (L : Lang Arity) [OpSem.Val L] where
  det : ∀ {e} {v₁ v₂ : L.Val}, OpP e v₁ → OpP e v₂ → v₁ = v₂

class Total (L : Lang Arity) [OpSem.Val L] where
  total : ∀ e, ∃ v : L.Val, OpP e v

inductive OpP' : STm L A → L.Val → Prop where
  | mk {e : Closed L} {v : L.Val}
    (w : OpP e v) (e? : STm L A) (he : e.toOpen = e?)
    : OpP' e? v

@[match_pattern]
def OpP.toOpen {e : Closed L} {v : L.Val} (w : OpP e v)
  : OpP' (A := A) e.toOpen v :=
  .mk w e.toOpen rfl

def OpP.toOpen_map {e : Closed L} {v : L.Val} (w : OpP e v) (f : A₁ → A₂)
  : OpP' (f <$> e.toOpen) v
  := e.map_toOpen f ▸ w.toOpen

theorem OpP'.map {e : STm L A₁} {v : L.Val} (w : OpP' e v) (f : A₁ → A₂)
  : OpP' (f <$> e) v
  := match w with | .mk w _ rfl => w.toOpen_map f

inductive OpW' : STm L A → L.Val → Type _ where
  | mk {e : Closed L} {v : L.Val}
    (w : OpW e v) (e? : STm L A) (he : e.toOpen = e?)
    : OpW' e? v

@[match_pattern]
def OpW.toOpen {e : Closed L} {v : L.Val} (w : OpW e v)
  : OpW' (A := A) e.toOpen v :=
  .mk w e.toOpen rfl

def OpW'.castIn {e₁ e₁' : STm L A} {v} (w : OpW' e₁' v) (he₁ : e₁ = e₁')
  : OpW' e₁ v
  := match w with | .mk w _ he => .mk w e₁ (he.trans he₁.symm)

@[simp]
theorem OpW.castIn_refl {e : STm L A} {v} (w : OpW' e v)
  : w.castIn rfl = w
  := by cases w; rfl

@[simp]
theorem OpW.castIn_castIn {e₁ e₁' e₁'' : STm L A} {v}
  (he₁ : e₁ = e₁') (he₁' : e₁' = e₁'') (w : OpW' e₁'' v)
  : (w.castIn he₁').castIn he₁ = w.castIn (he₁.trans he₁')
  := by cases he₁; cases he₁'; simp

def OpW'.map {e : STm L A₁} {v} (w : OpW' e v) (f : A₁ → A₂)
  : OpW' (f <$> e) v
  := match w with | .mk w _ h => .mk w _ (by cases h; simp)

theorem OpW'.map_id {e : STm L A} {v} (w : OpW' e v)
  : w.map id = w.castIn (by simp)
  := by cases w; rfl

theorem OpW'.map_map {e : STm L A₁} {v} (w : OpW' e v) (f : A₁ → A₂) (g : A₂ → A₃)
  : (w.map f).map g = (w.map (g ∘ f)).castIn (by rw [comp_map])
  := match w with
  | mk _ _ _ => rfl

theorem OpW'.map_comp {e : STm L A₁} {v} (w : OpW' e v) (f : A₁ → A₂) (g : A₂ → A₃)
  : w.map (g ∘ f) = ((w.map f).map g).castIn (by rw [comp_map])
  := by simp [OpW'.map_map]

inductive StepP (Store : L.Store A) : STm L A → STm L A → Prop where
  | sym {a v} : Store.GetP a v -> StepP Store (.sym a) (.const v)
  | op {arity} {o : L.Op arity} {es es' : Ix arity → STm L A} :
    (i : Ix arity)
    → StepP Store (es i) (es' i)
    → StepP Store (.op o es) (.op o es')
  | step
    {e : STm L A} {v : L.Val}
    (w : OpP' e v)
    : StepP Store e (.const v)

def StepP.map {S₁ : L.Store A₁} {S₂ : L.Store A₂} {e₁ e₁' : STm L A₁}
  (h : StepP S₁ e₁ e₁')
  (f : S₁.Hom S₂)
  : StepP S₂ (f.toFun <$> e₁) (f.toFun <$> e₁')
  := match h with
  | .sym h => .sym (f.mapGetP h)
  | .op i h => .op i (h.map f)
  | .step w => .step (w.map f.toFun)

inductive StepW (Store : L.Store A) : STm L A → STm L A → Type _ where
  | sym {a v} : Store.GetW a v -> StepW Store (.sym a) (.const v)
  | op {arity} {o : L.Op arity} {es es' : Ix arity → STm L A} :
    (i : Ix arity)
    → StepW Store (es i) (es' i)
    → StepW Store (.op o es) (.op o es')
  | step
    {e : STm L A} {v : L.Val}
    (w : OpW' e v)
    : StepW Store e (.const v)

def StepW.map {S₁ : L.Store A₁} {S₂ : L.Store A₂} {e₁ e₁' : STm L A₁}
  (h : StepW S₁ e₁ e₁')
  (f : S₁.Hom S₂)
  : StepW S₂ (f.toFun <$> e₁) (f.toFun <$> e₁')
  := match h with
  | .sym h => .sym (f.mapGetW h)
  | .op i h => .op i (h.map f)
  | .step w => .step (w.map f.toFun)

variable {Store : L.Store A}

def StepW.castIn {e₁ e₁'}
  (he₁ : e₁ = e₁')
  (w : StepW Store e₁' e₂)
  : StepW Store e₁ e₂
  := (he₁ ▸ w)

@[simp]
theorem StepW.castIn_refl {e₁} (w : StepW Store e₁ e₂)
  : w.castIn rfl = w := rfl

@[simp]
theorem StepW.castIn_castIn
  {e₁ e₁' e₁''} (he₁ : e₁ = e₁') (he₁' : e₁' = e₁'')
  (w : StepW Store e₁'' e₂)
  : (w.castIn he₁').castIn he₁ = w.castIn (he₁.trans he₁')
  := by cases he₁; cases he₁'; rfl

def StepW.castOut {e₂ e₂'}
  (w : StepW Store e₁ e₂)
  (he₂ : e₂ = e₂')
  : StepW Store e₁ e₂'
  := (he₂ ▸ w)

@[simp]
theorem StepW.castOut_refl {e₂} (w : StepW Store e₁ e₂)
  : w.castOut rfl = w := rfl

@[simp]
theorem StepW.castOut_castOut
  {e₂ e₂' e₂''} (he₂ : e₂ = e₂') (he₂' : e₂' = e₂'')
  (w : StepW Store e₁ e₂)
  : (w.castOut he₂).castOut he₂' = w.castOut (he₂.trans he₂')
  := by cases he₂; cases he₂'; rfl

theorem StepW.castIn_castOut
  {e₁ e₁' e₂ e₂'} (he₁ : e₁ = e₁') (he₂ : e₂ = e₂')
  (w : StepW Store e₁' e₂)
  : (w.castIn he₁).castOut he₂ = (w.castOut he₂).castIn he₁
  := by cases he₁; cases he₂; rfl

@[match_pattern]
def OpP.step
  {e : Closed L} {v : L.Val}
  (w : OpP e v)
  : StepP Store e.toOpen (.const v) :=
  .step w.toOpen

@[match_pattern]
def OpW.step
  {e : Closed L} {v : L.Val}
  (w : OpW e v)
  : StepW Store e.toOpen (.const v) :=
  .step w.toOpen

inductive BigStepP (Store : L.Store A) : STm L A → L.Val → Prop where
  | const {v} : BigStepP Store (.const v) v
  | small {e e' v} : StepP Store e e' → BigStepP Store e' v → BigStepP Store e v

inductive BigStepW (Store : L.Store A) : STm L A → L.Val → Type _ where
  | const {v} : BigStepW Store (.const v) v
  | small {e e' v} : StepW Store e e' → BigStepW Store e' v → BigStepW Store e v

def Defined (Store : L.Store A) (e : STm L A) : Prop := ∃v, BigStepP Store e v

structure Result (Store : L.Store A) (e : STm L A) : Type _ where
  val : L.Val
  w : BigStepW Store e val

structure PartialEvaluator (Store : L.Store A) : Type _ where
  eval : (e : STm L A) → Option (Result Store e)

end OpSem.Val

end STm

end Isotope
