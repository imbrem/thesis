import Isotope.LambdaIter.Named.Subst

/-! # Alpha-equivalence for named lambda-iter -/

namespace Isotope.LambdaIter.Named

variable [DecidableEq ν] {S : Signature τ}

/-- Independent named alpha-equivalence. Binder-renaming constructors require
both absence of a free target name and `CaptureSafe`, so they cannot capture a
free occurrence or move it beneath an existing same-named binder. -/
inductive Alpha : Tm ν S → Tm ν S → Prop where
  | refl (a) : Alpha a a
  | symm : Alpha a b → Alpha b a
  | trans : Alpha a b → Alpha b c → Alpha a c
  | op : Alpha a b → Alpha (.op f a) (.op f b)
  | let₁ : Alpha a a' → Alpha b b' → Alpha (.let₁ x a b) (.let₁ x a' b')
  | pair : Alpha a a' → Alpha b b' → Alpha (.pair a b) (.pair a' b')
  | let₂ : Alpha a a' → Alpha b b' → Alpha (.let₂ x y a b) (.let₂ x y a' b')
  | inl : Alpha a b → Alpha (.inl a) (.inl b)
  | inr : Alpha a b → Alpha (.inr a) (.inr b)
  | case : Alpha e e' → Alpha a a' → Alpha b b' →
      Alpha (.case e x a y b) (.case e' x a' y b')
  | abort : Alpha a b → Alpha (.abort a) (.abort b)
  | iter : Alpha a a' → Alpha b b' → Alpha (.iter a x b) (.iter a' x b')
  | let₁Rename (hfree : ¬b.Free y) (hsafe : CaptureSafe (.var y) b) :
      Alpha (.let₁ (some x) a b)
        (.let₁ (some y) a (Tm.substSafe x (.var y) b hsafe))
  | let₂RenameLeft (hfree : ¬b.Free z) (hsafe : CaptureSafe (.var z) b) :
      Alpha (.let₂ (some x) y a b)
        (.let₂ (some z) y a (Tm.substSafe x (.var z) b hsafe))
  | let₂RenameRight (hfree : ¬b.Free z) (hsafe : CaptureSafe (.var z) b) :
      Alpha (.let₂ x (some y) a b)
        (.let₂ x (some z) a (Tm.substSafe y (.var z) b hsafe))
  | caseRenameLeft (hfree : ¬a.Free z) (hsafe : CaptureSafe (.var z) a) :
      Alpha (.case e (some x) a y b)
        (.case e (some z) (Tm.substSafe x (.var z) a hsafe) y b)
  | caseRenameRight (hfree : ¬b.Free z) (hsafe : CaptureSafe (.var z) b) :
      Alpha (.case e x a (some y) b)
        (.case e x a (some z) (Tm.substSafe y (.var z) b hsafe))
  | iterRename (hfree : ¬b.Free y) (hsafe : CaptureSafe (.var y) b) :
      Alpha (.iter a (some x) b)
        (.iter a (some y) (Tm.substSafe x (.var y) b hsafe))

end Isotope.LambdaIter.Named
