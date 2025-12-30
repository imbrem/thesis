#import "../../syntax.typ": *

#show: show-syntax

#let def-cart-ty-sys = definition(name: "Cartesian Type System")[
  We define a _cartesian type system_ $ms("X")$ to consist of:
  - A set of _types_ $ms("X")$
  - A near-prelattice $(sle()) : ms("X") rfn ms("X")$ on base types, _weakening_
]

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
  $tywk(Σ lb("T"), Σ lb("T"'))$,
  $tywk(A, A')$,
  $tywk(Σ (lb("T"), lty(lb("f"), A)), Σ (lb("T")', lty(lb("f"), A')))$,
);
#let r-twk-pi = rule(
  name: $Π$,
  $tywk(Π lb("T"), Π lb("T"'))$,
  $tywk(A, A')$,
  $tywk(Π (lb("T"), fty(lb("f"), A)), Π (lb("T")', fty(lb("f"), A')))$,
);
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
      declare-rule(r-twk-unit, label: <twk-unit>),
      declare-rule(r-twk-zero, label: <twk-zero>),
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

#let def-ty-sys = definition(name: "Type System")[
  We define a _type system_ $ms("X")$ to consist of:
  - A set of _base types_ $ms("X")$
  - A set of _affine_ base types $affm : ms("X") rfn tunit$
  - A near-prelattice $(sle()) : ms("X") rfn ms("X")$ on base types, _weakening_
  - A _splitting_ relation $(splitr) : ms("X") rfn ms("X") × ms("X")$
  such that
  - Splitting $(splitr)$ is coassociative and cocommutative, i.e.
    $tysplits(X, Y, Z) <==> tysplits(X, Z, Y)$ and
    $
    (∃ X_(12) . tysplits(X_(123), X_(12), X_3) ∧ tysplits(X_(12), X_1, X_2))
    <==>
    (∃ X_(23) . tysplits(X_(123), X_1, X_(23)) ∧ tysplits(X_(23), X_2, X_3))
    $
  - If $tysplits(X, Y, Z)$ and $urel(affm, Z)$, then $tywk(X, Y)$ 
    ("affine components can be discarded")

  We say a base type $X$ is _relevant_ if $tysplits(X, X, X)$.

  We say a type system $ms("X")$ is _relevant_ if every type $X ∈ ms("X")$ is relevant;
  likewise, $ms("X")$ is _affine_ if every $X ∈ ms("X")$ is affine.
  If $ms("X")$ both affine and relevant, we say it is _cartesian_;
  in this case, we can recover all our structure from the weakening relation alone, since 
  $
  tysplits(X, Y, Z) <==> tywk(X, Y) ∧ tywk(X, Z)
  $
]

#def-ty-sys

#let fig-quant-lattice = figure(
  [
    #stack(
      dir: ltr,
      spacing: 4em,
      [
        $
                                    \
                                    \
          tqaff + 1 = tqaff + tqrel & = tqint #h(2em) &       q & kqwk tqint \
          tqaff + tqaff = tqint + q & = tqint \
                                    \
                  tqrel + 1 = 1 + 1 & = tqrel         &   tqlin & kqwk tqrel \
                      tqrel + tqrel & = tqrel         &          \
                                    \
                                    &                 &   tqlin & kqwk tqaff \
                                    \
                                    \
                              0 + q & = q             &       0 & kqwk tqaff \
                                    &                 & (n + 1) & kqwk tqrel
        $
      ],
      diagram(
        $
                               & tqint \
          tqaff edge("ur", ->) &       & tqrel edge("ul", ->) \
                               & tqlin edge("ul", ->) edge("ur", ->) //
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
    Join-semilattice of usages under $kqwk$
  ],
)

#fig-quant-lattice

#let r-quant-base = rule(
  name: "base",
  $tyquant(ms("U"), X, q)$,
  $tyquant(ms("U"), tybase(X), q)$,
)
#let r-quant-sigma = rule(
  name: $Σ$,
  $lquant(ms("U"), lb("L"), q)$,
  $tyquant(ms("U"), (Σ lb("L")), q)$,
);
#let r-quant-pi = rule(
  name: $Π$,
  $cquant(ms("U"), lb("T"), q)$,
  $tyquant(ms("U"), (Π lb("T")), q)$,
);

#let r-quant-sigma-nil = rule(
  name: [$Σ$-nil],
  $cquant(ms("U"), ·, q)$,
);
#let r-quant-sigma-cons = rule(
  name: [$Σ$-cons],
  $cquant(ms("U"), lb("L"), q)$,
  $tyquant(ms("U"), A, q)$,
  $cquant(ms("U"), (lb("L"), lty(lb("l"), A)), q)$,
);

#let r-quant-pi-nil = rule(
  name: [$Π$-nil],
  $lquant(ms("U"), ·, q)$,
);
#let r-quant-pi-cons = rule(
  name: [$Π$-cons],
  $lquant(ms("U"), lb("T"), q)$,
  $tyquant(ms("U"), A, q)$,
  $lquant(ms("U"), (lb("T"), fty(lb("f"), A)), q)$,
)

#let r-quant-sigma-forall = rule(
  name: $Σ$,
  $∀ lty(lb("l"), A) ∈ lb("L") . tyquant(ms("U"), A, q)$,
  $tyquant(ms("U"), (Σ lb("L")), q)$,
);
#let r-quant-pi-forall = rule(
  name: $Π$,
  $∀ fty(lb("f"), A) ∈ lb("L") . tyquant(ms("U"), A, q)$,
  $tyquant(ms("U"), (Π lb("L")), q)$,
);

#let r-utywk-base = rule(
  name: "base",
  $X sle(ms("U")) Y$,
  $utywk(ms("U"), tybase(X), tybase(Y))$,
)
#let r-utywk-sigma = rule(
  name: $Σ$,
  $utywk(ms("U"), Σ lb("T"), Σ lb("T"'))$,
  $utywk(ms("U"), A, A')$,
  $utywk(ms("U"), Σ (lb("T"), lty(lb("f"), A)), Σ (lb("T")', lty(lb("f"), A')))$,
);
#let r-utywk-pi = rule(
  name: $Π$,
  $utywk(ms("U"), Π lb("T"), Π lb("T"'))$,
  $utywk(ms("U"), A, A')$,
  $utywk(ms("U"), Π (lb("T"), fty(lb("f"), A,)), Π (lb("T")', fty(lb("f"), A')))$,
);
#let r-utywk-zero = rule(
  name: $tzero$,
  $utywk(ms("U"), tzero, A)$,
);
#let r-utywk-unit = rule(
  name: $tunit$,
  $isaff(ms("U"), X)$,
  $utywk(ms("U"), tybase(X), tunit)$,
);

#let r-ty-split-left = rule(
  name: "left",
  $utysplits(ms("U"), A, 1, A)$,
)
#let r-ty-split-right = rule(
  name: "right",
  $utysplits(ms("U"), A, A, 1)$,
)
#let r-ty-split-both = rule(
  name: "both",
  $isrel(ms("U"), A)$,
  $utysplits(ms("U"), A, A, A)$,
)
#let r-ty-split-pi = rule(
  name: "Π",
  $utysplits(ms("U"), Π lb("T"), Π lb("T")_kwl, Π lb("T")_kwr)$,
  $utysplits(ms("U"), A, A_kwl, A_kwr)$,
  $utysplits(
    ms("U"),
    Π (lb("T"), fty(lb("f"), A)),
    (lb("T")_kwl, fty(lb("f"), A_kwl)), (lb("T")_kwr, fty(lb("f"), A_kwr))
  )$,
)

#let fig-r-utywk = figure(
  [
    #rule-set(
      declare-rule(r-quant-base, label: <quant-base>),
      declare-rule(r-quant-sigma, label: <quant-sigma>),
      declare-rule(r-quant-pi, label: <quant-pi>),
      declare-rule(r-quant-sigma-nil, label: <quant-sigma-nil>),
      declare-rule(r-quant-sigma-cons, label: <quant-sigma-cons>),
      declare-rule(r-quant-pi-nil, label: <quant-pi-nil>),
      declare-rule(r-quant-pi-cons, label: <quant-pi-cons>),
    )
    \
    #rule-set(
      declare-rule(r-utywk-base, label: <utywk-base>),
      declare-rule(r-utywk-sigma, label: <utywk-sigma>),
      declare-rule(r-utywk-pi, label: <utywk-pi>),
      declare-rule(r-utywk-unit, label: <utywk-unit>),
      declare-rule(r-utywk-zero, label: <utywk-zero>),
    )
    \
    #rule-set(
      declare-rule(r-ty-split-left),
      declare-rule(r-ty-split-right),
      declare-rule(r-ty-split-both),
      declare-rule(r-ty-split-pi),
      // declare-rule(r-ctx-split)
    )
    \
  ],
  caption: [Linearity for simple types $sty(ms("X"))$],
)

#fig-r-utywk

/*
#let r-isaff-base = rule(
  name: "base",
  $isaff(ms("U"), X)$,
  $isaff(ms("U"), tybase(X))$
);
#let r-isaff-sigma = rule(
  name: $Σ$,
  $∀ lb("l")(A) ∈ lb("L") . isaff(ms("U"), A)$,
  $isaff(ms("U"), Σ lb("L"))$,
);
#let r-isaff-pi = rule(
  name: $Π$,
  $∀ lb("l")(A) ∈ lb("L") . isaff(ms("U"), A)$,
  $isaff(ms("U"), Π lb("L"))$,
);

#let r-isrel-base = rule(
  name: "base",
  $isrel(ms("U"), X)$,
  $isrel(ms("U"), tybase(X))$
);
#let r-isrel-sigma = rule(
  name: $Σ$,
  $∀ lb("l")(A) ∈ lb("L") . isrel(ms("U"), A)$,
  $isrel(ms("U"), Σ lb("L"))$,
);
#let r-isrel-pi = rule(
  name: $Π$,
  $∀ lb("l")(A) ∈ lb("L") . isrel(ms("U"), A)$,
  $isrel(ms("U"), Π lb("L"))$,
);
*/

#let r-ctx-nil = rule(
  name: "nil",
  $uctxwk(ms("U"), ·, ·)$,
)
#let r-ctx-cons = rule(
  name: "cons",
  $uctxwk(ms("U"), Γ, Δ)$,
  $tywk(A, B)$,
  $qwk(q, q')$,
  $uctxwk(ms("U"), #$Γ, x : A^q$, #$Δ, x : B^(q')$)$,
)
#let r-ctx-skip = rule(
  name: "skip",
  $uctxwk(ms("U"), Γ, Δ)$,
  $tywk(A^q, tunit^0)$,
  $uctxwk(ms("U"), #$Γ, x : A^q$, Δ)$,
)
#let r-ctx-split = rule(
  name: "both",
  $usplits(ms("U"), Γ, Γ_kwl, Γ_kwr)$,
  $utysplits(ms("U"), A, A_kwl, A_kwr)$,
  $q = q_kwl + q_kwr$,
  $usplits(ms("U"), #$Γ, x : A^q$, #$Γ_kwl, x : A_kwl^(q_kwl)$, #$Γ_kwr, x : A_kwr^(q_kwr)$)$,
)

#let fig-r-uctxwk = figure(
  [
    #rule-set(
      declare-rule(r-ctx-nil, label: <uctx-nil>),
      declare-rule(r-ctx-cons, label: <uctx-cons>),
      declare-rule(r-ctx-skip, label: <uctx-skip>),
      declare-rule(r-ctx-split, label: <uctx-split>),
    )
    \
  ],
  caption: [Weakening and splitting for annotated contexts],
)

#fig-r-uctxwk
