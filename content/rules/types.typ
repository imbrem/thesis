#import "../../syntax.typ": *

#show: show-syntax

#let tyrel(X, Y) = $ms("TyRel")(#X, #Y)$

#let def-ty-rel = definition(name: "Typing Relation")[
  We define a _typing relation_ $ms("W") : tyrel(ms("X"), ms("Y"))$ 
  from typing discipline $ms("X")$ to typing discipline $ms("Y")$
  to be 
  - a set of _programs_ $p ∈ |ms("W")|$
  - a $|P|$-indexed family of relations $ms("W")_p : ms("X") rfn ms("Y")$

  We call $ms("W")$ a _type system_ if each $ms("W")_p$ is a profunctor 
  (w.r.t. the weakening order).
]

#def-ty-rel

#let def-res-disc = definition(name: "Resource Discipline")[
  We define a _resource discipline_ $ms("X")$ to consist of a type discipline $ms("X")$
  equipped with a _splitting_ relation $(splitr) : ms("X") rfn ms("X") × ms("X")$
  such that
  - Splitting $(splitr)$ is coassociative and cocommutative, i.e.
    $tysplits(X, Y, Z) <==> tysplits(X, Z, Y)$ and
    $
      (∃ X_(12) . (tysplits(X_(123), X_(12), X_3)) ∧ (tysplits(X_(12), X_1, X_2))) \
      <==> \
      (∃ X_(23) . (tysplits(X_(123), X_1, X_(23))) ∧ (tysplits(X_(23), X_2, X_3)))
    $
  - If $tysplits(X, Y, Z)$ and $urel(saff, Z)$, then $tywk(X, Y)$
    ("affine components can be discarded")
  - If $urel(sidm, X)$ iff $tysplits(X, X, X)$

  We note that, if $ms("X")$ is cartesian, our splitting relation is uniquely determined by
  $
    tysplits(X, Y, Z) <==> tywk(X, Y) ∧ tywk(X, Z)
  $

]

#def-res-disc

#let fig-ty-grammar = figure(
  [
    #grid(
      align: left,
      columns: 2,
      gutter: (2em, 2em),
      bnf(
        Prod($A$, {
          Or[$tybase(X)$][_base type_ $X ∈ ms("X")$]
          Or[$Σ lb("L")$][_Σ (coproduct)_]
          Or[$Π lb("T")$][_Π (product)_]
        }),
      ),
      bnf(
        Prod($lb("L")$, {
          Or[$·$][]
          Or[$lb("L"), lty(lb("l"), A)$][where $lb("l") ∉ lb("L")$]
        }),
        Prod($lb("T")$, {
          Or[$·$][]
          Or[$lb("T"), fty(lb("f"), A)$][where $lb("f") ∉ lb("T")$]
        }),
      ),
    )
    $
      A × B & := Π ( kwl : A, kwr : B ) & #h(3em) & mb(1) & := Π (·) \
      A + B & := Σ ( kwl(A), kwr(B) )   &         & mb(0) & := Σ (·)
    $
    $
      Π [A_0,...,A_(n - 1)] & = Π_i A_i & := Π ( lb("p")_0 : A_0, ..., lb("p")_(n - 1) : A_(n - 1) ) \
      Σ [A_0,...,A_(n - 1)] & = Σ_i A_i &   := Σ ( lb("i")_0(A_0), ..., lb("i")_(n - 1)(A_(n - 1)) )
    $
    \
  ],
  caption: [
    Grammar for simple types $A ∈ sty(ms("X"))$ parametrized by base types $ms("X")$.
  ],
  kind: image,
);

#fig-ty-grammar

#let r-twk-base = rule(
  name: "base",
  $X sle() Y$,
  $tywk(tybase(X), tybase(Y))$,
);
#let r-twk-sigma = rule(
  name: $Σ$,
  $tywk(Σ lb("L"), Σ lb("L"'))$,
  $tywk(A, A')$,
  $tywk(Σ (lb("L"), lty(lb("l"), A)), Σ (lb("L")', lty(lb("l"), A')))$,
);
#let r-twk-pi = rule(
  name: $Π$,
  $tywk(Π lb("T"), Π lb("T"'))$,
  $tywk(A, A')$,
  $tywk(Π (lb("T"), fty(lb("f"), A)), Π (lb("T")', fty(lb("f"), A')))$,
);
#let r-twk-sigma-perm = rule(
  name: [$Σ$-perm],
  $σ "perm"$,
  $tywk(Σ lb("L"), A)$,
  $tywk(Σ (σ · lb("L")), A)$,
)
#let r-twk-pi-perm = rule(
  name: [$Π$-perm],
  $σ "perm"$,
  $tywk(Π lb("T"), A)$,
  $tywk(Π (σ · lb("T")), A)$,
)
#let r-twk-zero = rule(
  name: $tzero$,
  $tywk(tzero, A)$,
);
#let r-twk-unit = rule(
  name: $tunit$,
  $urel(saff, A)$,
  $tywk(A, tunit)$,
);

#let fig-r-twk = figure(
  [
    #rule-set(
      declare-rule(r-twk-base, label: <twk-base>),
      declare-rule(r-twk-sigma, label: <twk-sigma>),
      declare-rule(r-twk-pi, label: <twk-pi>),
      declare-rule(r-twk-sigma-perm, label: <twk-sigma-perm>),
      declare-rule(r-twk-pi-perm, label: <twk-pi-perm>),
      declare-rule(r-twk-zero, label: <twk-zero>),
      declare-rule(r-twk-unit, label: <twk-unit>),
    )
    \
  ],
  caption: [Weakening for simple types $sty(ms("X"))$],
)

#fig-r-twk

#let r-cart-twk-unit = rule(
  name: $tunit$,
  $urel(saff, A)$,
  $tywk(A, tunit)$,
);

#let fig-r-cart-twk = figure(
  [
    #rule-set(
      declare-rule(r-twk-base, label: <cart-twk-base>),
      declare-rule(r-twk-sigma, label: <cart-twk-sigma>),
      declare-rule(r-twk-pi, label: <cart-twk-pi>),
      declare-rule(r-twk-sigma-perm, label: <cart-twk-sigma-perm>),
      declare-rule(r-twk-pi-perm, label: <cart-twk-pi-perm>),
      declare-rule(r-twk-zero, label: <cart-twk-zero>),
      declare-rule(r-cart-twk-unit, label: <cart-twk-unit>),
    )
    \
  ],
  caption: [Weakening for cartesian simple types $sty(ms("X"))$],
)

#fig-r-cart-twk

/*
#let fig-ty-lattice = figure(
  [
    $
      X ⊔_(sty(ms("X"))) Y = cases(X ⊔_X Y "if defined", tunit "otherwise")
      quad quad quad
      X ⊓_(sty(ms("X"))) Y = cases(X ⊓_X Y "if defined", tzero "otherwise")
      \
      A ⊔ tunit = tunit ⊔ A = tunit quad quad
      A ⊔ tzero = tzero ⊔ A = A quad quad
      A ⊓ tunit = tunit ⊓ A = A quad quad
      A ⊓ tzero = tzero ⊓ A = tzero
    $
    $
      Σ lb("L") ⊔ Σ lb("L'") & :=
                               Σ (lty(lb("l"), labhi(lb("L"), lb("l")) ⊔ labhi(lb("L"), lb("l")))
                                 | lb("l") ∈ lab(lb("L")) ∪ lab(lb("L"'))) \
      Π lb("T") ⊔ Π lb("T'") & :=
                               Π (fty(lb("l"), fldhi(lb("T"), lb("l")) ⊔ fldhi(lb("X"'), lb("l")))
                                 | lb("l") ∈ fld(lb("T")) ∩ fld(lb("X"'))) \
      Σ lb("L") ⊓ Σ lb("L'") & :=
                               Σ (lty(lb("l"), lablo(lb("L"), lb("l")) ⊓ lablo(lb("L"), lb("l")))
                                 | lb("l") ∈ lab(lb("L")) ∩ lab(lb("L"'))) \
      Π lb("T") ⊓ Π lb("T'") & :=
                               Π (fty(lb("l"), fldlo(lb("T"), lb("l")) ⊓ fldlo(lb("T"), lb("l")))
                                 | lb("l") ∈ fld(lb("T")) ∪ fld(lb("X"')))
    $
    where
    $
      lablo(lb("L"), lb("l")) = cases(
        A "if" lty(lb("l"), A) ∈ lb("L"),
        tzero "otherwise"
      ) quad quad
      labhi(lb("L"), lb("l")) = cases(
        A "if" lty(lb("l"), A) ∈ lb("L"),
        tunit "otherwise"
      )
    $
    $
      fldlo(lb("T"), lb("f")) = cases(
        A "if" fty(lb("f"), A) ∈ lb("T"),
        tzero "otherwise"
      ) quad quad
      fldhi(lb("T"), lb("f")) = cases(
        A "if" fty(lb("f"), A) ∈ lb("T"),
        tunit "otherwise"
      )
    $
    $
      lab(·) = ∅ quad
      lab(lb("L"), lty(lb("l"), A)) = lab(lb("L")) ∪ { lb("l") } quad
      fld(·) = ∅ quad
      fld(lb("T"), fty(lb("f"), A)) = fld(lb("T")) ∪ { lb("f") }
    $

    \
  ],
  caption: [Lattice structure on simple types $sty(ms("X"))$],
);

#fig-ty-lattice
*/

#let r-ctxwk-nil = rule(
  name: "Π-nil",
  $cwk(Γ, ·)$,
)
#let r-ctxwk-cons = rule(
  name: "Π-cons",
  $clbwk(Γ, Δ)$,
  $tywk(A, B)$,
  $cwk(#$Γ, x : A$, #$Δ, x : A$)$,
);
#let r-ctxwk-perm = rule(
  name: [Π-perm],
  $σ "perm"$,
  $cwk(Γ, Δ)$,
  $cwk(σ · Γ, Δ)$,
);

#let r-lbwk-nil = rule(
  name: "Σ-nil",
  $lbcwk(·, ms("K"))$,
)
#let r-lbwk-cons = rule(
  name: "Σ-cons",
  $lbcwk(ms("L"), ms("K"))$,
  $tywk(A, B)$,
  $cwk(#$ms("L"), lb("l")(A)$, #$ms("K"), lb("l")(B)$)$,
);
#let r-lbwk-perm = rule(
  name: [Σ-perm],
  $σ "perm"$,
  $lbcwk(ms("L"), ms("K"))$,
  $lbcwk(σ · ms("L"), ms("K"))$,
);

#let r-clwk-nil = rule(
  name: "ΣΠ-nil",
  $clbwk(·, cal("K"))$,
)
#let r-clwk-cons = rule(
  name: "ΣΠ-cons",
  $clbwk(cal("L"), cal("K"))$,
  $cwk(Γ, Δ)$,
  $tywk(A, B)$,
  $clbwk(#$cal("L"), clty(lb("l"), Γ, A)$, #$cal("K"), clty(lb("l"), Δ, B)$)$,
);
#let r-clwk-perm = rule(
  name: [ΣΠ-perm],
  $σ "perm"$,
  $clbwk(cal("L"), cal("K"))$,
  $clbwk(σ · cal("L"), cal("K"))$,
);

#let fig-r-cwk = figure(
  [
    #rule-set(
      declare-rule(r-ctxwk-nil, label: <ctxwk-nil>),
      declare-rule(r-ctxwk-cons, label: <ctxwk-cons>),
      declare-rule(r-ctxwk-perm, label: <ctxwk-perm>),
      declare-rule(r-lbwk-nil, label: <lbwk-nil>),
      declare-rule(r-lbwk-cons, label: <lbwk-cons>),
      declare-rule(r-lbwk-perm, label: <lbwk-perm>),
      declare-rule(r-clwk-nil, label: <clwk-nil>),
      declare-rule(r-clwk-cons, label: <clwk-cons>),
      declare-rule(r-clwk-perm, label: <clwk-perm>),
    )
    \
  ],
  caption: [Weakening for cartesian contexts],
)

#fig-r-cwk
