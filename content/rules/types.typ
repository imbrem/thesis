#import "../../syntax.typ": *

#show: show-syntax

#let def-ty-sys = definition(name: "Type System")[
  We define a _type system_ $ms("X")$ to consist of:
  - A set of _types_ $ms("X")$
  - A near-prelattice $X sle() Y$ on base types, _weakening_
  - An upper set $saff ⊆ X$ of _affine_ types
  - A lower set $srel ⊆ X$ of _relevant types_

  We say two types $X, Y$ are _equivalent_, written $X ≈ Y$, if $X sle() Y$ and $Y sle() X$.

  We say a type system is _cartesian_ if $saff = srel = X$.
]

#let def-res-sys = definition(name: "Type System")[
  We define a _resource system_ $ms("X")$ to consist of a type system $ms("X")$
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
  - If $urel(srel, X)$ iff $tysplits(X, X, X)$

  We note that, if $ms("X")$ is cartesian, our splitting relation is uniquely determined by
  $
    tysplits(X, Y, Z) <==> tywk(X, Y) ∧ tywk(X, Z)
  $

]

#def-res-sys

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
          Or[$lb("L"), lty(lb("l"), A)$][]
        }),
        Prod($lb("T")$, {
          Or[$·$][]
          Or[$lb("T"), fty(lb("f"), A)$][]
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
    Grammar for simple types parametrized by base types $ms("X")$.
    We treat $lb("L"), lb("T")$ as _label-indexed families_ of types,
    and in particular quotient by order.
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

#let fig-r-cwk = figure(
  [
    #rule-set(
      declare-rule(r-ctxwk-nil, label: <ctxwk-nil>),
      declare-rule(r-ctxwk-cons, label: <ctxwk-cons>),
      declare-rule(r-lbwk-nil, label: <lbwk-nil>),
      declare-rule(r-lbwk-cons, label: <lbwk-cons>),
      declare-rule(r-clwk-nil, label: <clwk-nil>),
      declare-rule(r-clwk-cons, label: <clwk-cons>),
    )
    \
  ],
  caption: [Weakening for cartesian contexts],
)

#fig-r-cwk

#let fig-quant-lattice = figure(
  [
    #stack(
      dir: ltr,
      spacing: 4em,
      [
        $
                                    \
                                    \
          tqaff + 1 = tqaff + tqrel & = tqint #h(2em) & tqint & kqwk q \
          tqaff + tqaff = tqint + q & = tqint \
                                    \
                  tqrel + 1 = 1 + 1 & = tqrel         & tqrel & kqwk tqlin \
                      tqrel + tqrel & = tqrel         &        \
                                    \
                                    &                 & tqaff & kqwk tqlin \
                                    \
                                    \
                              0 + q & = q             & tqaff & kqwk 0 \
                                    &                 & tqrel & kqwk (n + 1)
        $
      ],
      diagram(
        $
                               & tqint \
          tqaff edge("ur", <-) &       & tqrel edge("ul", <-) \
                               & tqlin edge("ul", <-) edge("ur", <-) //
                                   \
          dem(0) edge("uu", "--", stroke: cdem) //
                               & dem(1) edge("u", "=", stroke: cdem) //
                                       & dem(2) edge("uu", "--", stroke: cdem) //
                                                              & dem(3) edge("uul", "--", stroke: cdem) //
                                                                  & ... edge("uull", "--", stroke: cdem)
        $,
      ),
    )
    \
  ],
  caption: [
    Meet-semilattice of usage obligations under $kqwk$, 
    going from "less defined/less restricted" to "more defined/more restricted."
  ],
)

#fig-quant-lattice
