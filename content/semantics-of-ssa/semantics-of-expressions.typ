#import "../../syntax.typ": *
#import "../../todos.typ": *

#import "../rules/twk.typ": *
#import "../rules/hasty.typ": *

#show: show-syntax

#definition[
  #todo[
    Definition: a $cal(V)$-enriched SSA model over a function space $ms("F")$
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

#todo[
  Lore about derivations ; coherence
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

#todo[Type weakening composes]

#dntty($ctxwk(Γ, Δ)$, $cal(C)_⊥(Π ⟦Γ⟧, Π ⟦Δ⟧)$)

$
  ⟦ctxwk(Γ, Δ)⟧ := ⟦tywk(Π Γ, Π Δ)⟧
$

#todo[Var weakening composes]

#dntty($lbctxwk(ms("L"), ms("M"))$, $cal(C)_⊥(Σ ⟦ms("L")⟧, Σ ⟦ms("M")⟧)$)

$
  ⟦lbctxwk(ms("L"), ms("M"))⟧ := ⟦tywk(Σ ms("L"), Σ ms("M"))⟧
$

#todo[Label weakening composes]

$
  ∀ f : cal(C)(A, B) . clet(f) := Δ_A ; A ⊗ f : cal(C)(A, A ⊗ B)
$

$
  ∀ f : cal(C)(A, Σ icol("B")) . ccase(f) := clet(l) ; idistl(A, icol("B"))
  : cal(C)(A, Σ (A ⊗ icol("B")))
$

#todo[let theorems]

#dntty($hasty(Γ, a, A)$, $cal(C)(Π ⟦Γ⟧, ⟦A⟧)$)

#eqn-set(
  dntdef(r-var, $π_x$),
  dntdef(r-coe, $⟦hasty(Γ, a, A)⟧ ; ⟦tywk(A, A')⟧$),
)

#eqn-astack(
  dntdef(r-app, $clet(⟦hasty(Γ, a, A)⟧) ; ⟦isfn(Γ, a, A, B)⟧$),
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
    $
  )
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

#theorem(name: "Weakening")[
  #todo[this]
]

#corollary(name: "Coherence")[
  #todo[this]
]

#definition[
  #todo[
    Definition: a $cal(V)$-enriched SSA model over a function space $ms("F")$
    w/ effect system $cal(E)$
  ]
]

#theorem(name: "Soundness (Effect)")[
  #todo[this]
]

#theorem(name: "Soundness (Substitution)")[
  #todo[this]
]

#theorem(name: "Soundness (Equivalence)")[
  #todo[this]
]

#theorem(name: "Completeness (Equivalence)")[
  #todo[this]
]

#todo[
  Definition: a $cal(V)$-enriched SSA model over a function space $ms("F")$
  w/ _linear_ effect system $cal(E)$
]

#theorem(name: "Soundness (Refinement)")[
  #todo[this]
]

#theorem(name: "Completeness (Refinement)")[
  #todo[this]
]