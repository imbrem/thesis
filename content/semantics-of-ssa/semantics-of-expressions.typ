#import "../../syntax.typ": *
#import "../../todos.typ": *

#import "../rules/types.typ": *
#import "../rules/hasty.typ": *

#show: show-syntax

#definition[
  #todo-inline[
    a $cal(V)$-enriched SSA model over a function space $ms("F")$
  ]
]

#todo[
  Acyclic expression lore???
]

$
  ⟦Σ lb("L")⟧ = Σ ⟦lb("L")⟧
  quad quad
  ⟦lb("L")⟧ = (lb("l") ↦ ⟦A⟧ | lty(lb("l"), A) ∈ lb("L"))
  \
  ⟦Π lb("X")⟧ = Π ⟦lb("X")⟧
  quad quad
  ⟦lb("X")⟧ = (lb("f") ↦ ⟦A⟧ | fty(lb("f"), A) ∈ lb("X"))
$

$
  ⟦cal(K)⟧ = (lb("l") ↦ Π ⟦Γ⟧ ⊗ ⟦A⟧ | clty(lb("l"), Γ, A) ∈ cal(K))
$

#todo[
  Text about coherence notation: for $D: deriv(hasty(Γ, a, A))$, 
  write $⟦D⟧$ as $⟦hasty(Γ, a, A)⟧$.

  Justified now by unique argument. Justified later by coherence.
]

#dntty($tywk(A, B)$, $cal(C)_⊥(⟦A⟧, ⟦B⟧)$)

#eqn-set(
  dntdef(r-twk-base, $⟦X sle(ms("X")) Y⟧$),
  dntdef(r-twk-zero, $0_B$),
  dntdef(r-twk-unit, $!_A$),
)
#eqn-astack(
  dntdef(r-twk-sigma, $α^+ ; ⟦tywk(Σ lb("L"), Σ lb("L")')⟧ + ⟦tywk(A, A')⟧ ; α^+$),
  dntdef(r-twk-pi, $α^⊗ ; ⟦tywk(Π lb("L"), Π lb("L")')⟧ ⊗ ⟦tywk(A, A')⟧ ; α^⊗$),
)

#lemma(name: "Coherence (Type weakening)")[
  For all derivations $D, D' : deriv(tywk(A, B))$, we have that $⟦D⟧ = ⟦D'⟧$.
  //
  In particular, if $A = B$, then $⟦D⟧ = id_(⟦A⟧)$.
]

#dntty($cwk(Γ, Δ)$, $cal(C)_⊥(Π ⟦Γ⟧, Π ⟦Δ⟧)$)

$
  ⟦cwk(Γ, Δ)⟧ := ⟦tywk(Π Γ, Π Δ)⟧
$

#lemma(name: "Coherence (Weakening)")[
  For all derivations $D, D' : deriv(cwk(Γ, Δ))$, we have that $⟦D⟧ = ⟦D'⟧$.
  //
  In particular, if $Γ = Δ$, then $⟦D⟧ = id_(Π ⟦Γ⟧)$.
]

#dntty($lbcwk(ms("L"), ms("K"))$, $cal(C)_⊥(Σ ⟦ms("L")⟧, Σ ⟦ms("K")⟧)$)

$
  ⟦lbcwk(ms("L"), ms("K"))⟧ := ⟦tywk(Σ ms("L"), Σ ms("K"))⟧
$

#lemma(name: "Coherence (Label weakening)")[
  For all derivations $D, D' : deriv(lbcwk(ms("L"), ms("K")))$, we have that $⟦D⟧ = ⟦D'⟧$.
  //
  In particular, if $ms("L") = ms("K")$, then $⟦D⟧ = id_(Σ ⟦ms("L")⟧)$.
]

#dntty($clbwk(cal("L"), cal("K"))$, $cal(C)_⊥(Σ ⟦cal("L")⟧, Σ ⟦cal("K")⟧)$)

#eqn-set(
  dntdef(r-clwk-nil, $0_(Σ ms("K"))$),
  dntdef(r-clwk-cons, $α^+ ; ⟦clbwk(cal("L"), cal("K"))⟧ + (⟦cwk(Γ, Δ)⟧ ⊗ ⟦tywk(A, B)⟧) ; α^+$),
)

#lemma(name: "Coherence (Control weakening)")[
  For all derivations $D, D' : deriv(lbcwk(cal("L"), cal("K")))$, we have that $⟦D⟧ = ⟦D'⟧$.
  //
  In particular, if $cal("L") = cal("K")$, then $⟦D⟧ = id_(Σ ⟦cal("K")⟧)$.
]

$
  ∀ f : cal(C)(A, B) . clet(f) := Δ_A ; A ⊗ f : cal(C)(A, A ⊗ B)
$

$
  ∀ f : cal(C)(A, Σ icol("B")) . ccase(f) := clet(l) ; idistl(A, icol("B"))
  : cal(C)(A, Σ (A ⊗ icol("B")))
$

#dntty($hasty(Γ, a, A)$, $cal(C)(Π ⟦Γ⟧, ⟦A⟧)$)

#eqn-set(
  dntdef(r-var, $π_x$),
  dntdef(r-coe, $⟦hasty(Γ, a, A)⟧ ; ⟦tywk(A, A')⟧$),
)

#eqn-astack(
  dntdef(r-app, $clet(⟦hasty(Γ, a, A)⟧) ; ⟦isfn(Γ, f, A, B)⟧$),
)

#eqn-set(
  dntdef(r-inj, $⟦hasty(Γ, a, A)⟧ ; ι_lb("l")$),
  dntdef(r-proj, $⟦hasty(Γ, e, Π (fty(lb("f"), A)))⟧ ; π_lb("f")$),
  dntdef(r-tuple, $⟦istup(Γ, E, lb("T"))⟧$),
)

#eqn-astack(
  dntdef(
    r-cases,
    $
      ccase(⟦hasty(Γ, e, Σ lb("L"))⟧)
      ; ⟦isebrs(Γ, lb("L"), M, A)⟧
    $,
  ),
  dntdef(
    r-let,
    $
      clet(⟦hasty(Γ, a, A)⟧) ; α^⊗ ; ⟦hasty(#$Γ, x : A$, b, B)⟧
    $,
  ),
  dntdef(
    r-iter,
    $
      clet(⟦hasty(Γ, a, A)⟧) ; (ccase(⟦hasty(Γ, e, B + A)⟧))^† ; rpi
    $,
  ),
)

#dntty($istup(Γ, E, lb("T"))$, $cal(C)(Π ⟦Γ⟧, Π ⟦lb("T")⟧)$)

#eqn-set(
  dntdef(r-pi-nil, $!_(Π⟦Γ⟧)$),
  dntdef(r-pi-cons, $Δ_(Π⟦Γ⟧) ; ⟦istup(Γ, E, lb("T"))⟧ ⋉ ⟦hasty(Γ, e, A)⟧ ; α^⊗$),
)

#dntty($kebrs(cal(K), M, A)$, $cal(C)(Σ ⟦cal(K)⟧, A)$)

#eqn-set(
  dntdef(r-csigma-nil, $0_A$),
  dntdef(
    r-csigma-cons,
    $α^+ ; ⟦kebrs(cal(K), M, A)⟧ + ⟦hasty(#$Γ, x : B$, a, A)⟧ ; ∇_⟦A⟧$,
  ),
)

#lemma(name: "Weakening")[
  For all derivations $D : deriv(hasty(Γ, a, A))$, $D' : deriv(hasty(Δ, a, A))$,
  given $cwk(Γ, Δ)$, we have that
  $⟦D'⟧ = ⟦cwk(Γ, Δ)⟧ ; ⟦D⟧$.

  In particular, it follows that, if $Γ = Δ$, $⟦D⟧ = ⟦D'⟧$.
]

#definition[
  #todo-inline[
    a $cal(V)$-enriched SSA model over a function space $ms("F")$
    w/ effect system $cal(E)$
  ]
]

#lemma(name: "Soundness (Effect)")[
  If $ehasty(Γ, ε, a, A)$, then $⟦hasty(Γ, a, A)⟧ : cal(C)_ε (Π ⟦Γ⟧, ⟦A⟧)$
]

#lemma(name: "Soundness (Substitution)")[
  #todo-inline[this]
]

#definition[
  #todo-inline[
    a $cal(V)$-enriched SSA model modeling an equational theory $req$
  ]
]

#theorem(name: "Soundness (Equivalence)")[
  Given $tyeq(Γ, req, a, b, A)$ and $cal(M) ⊧ req$, we have
  $
  ⟦hasty(Γ, a, A)⟧_cal(M) = ⟦hasty(Γ, b, A)⟧_cal(M)
  $
]

#theorem(name: "Completeness (Equivalence)")[
  Given $hasty(Γ, a, A)$ and $hasty(Γ, b, A)$, we have
  $
    tyeq(Γ, req, a, b, A) 
    <==> (∀ cal(M) ⊧ req . ⟦hasty(Γ, a, A)⟧_cal(M) = ⟦hasty(Γ, b, A)⟧_cal(M))
  $
]


#definition[
  #todo-inline[
    a $cal(V)$-enriched SSA model over a function space $ms("F")$
    w/ _linear_ effect system $cal(E)$
  ]
]

#lemma(name: "Soundness (Directed Substitution)")[
  #todo-inline[this]
]


#definition[
  #todo-inline[
    a $cal(V)$-enriched SSA model modeling a refinement theory $rref$
  ]
]

#theorem(name: "Soundness (Refinement)")[
  Given $tyref(Γ, rref, a, b, A)$ and $cal(M) ⊧ rref$, we have
  $
  ⟦hasty(Γ, a, A)⟧_cal(M) ->> ⟦hasty(Γ, b, A)⟧_cal(M)
  $
]

#theorem(name: "Completeness (Refinement)")[
  Given $hasty(Γ, a, A)$ and $hasty(Γ, b, A)$, we have
  $
    tyref(Γ, rref, a, b, A) 
    <==> (∀ cal(M) ⊧ rref . ⟦hasty(Γ, a, A)⟧_cal(M) ->> ⟦hasty(Γ, b, A)⟧_cal(M))
  $
]