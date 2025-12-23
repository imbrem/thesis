#import "../../syntax.typ": *
#import "../../todos.typ": *

#import "../rules/twk.typ": *
#import "../rules/hasty.typ": *

#show: show-syntax

#todo[
  Definition: a $cal(V)$-enriched SSA model over a function space $ms("F")$
]

#todo[
  Describe acyclic expression lore???
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

#dntty($ctxwk(Γ, Δ)$, $cal(C)_⊥(Π ⟦Γ⟧, Π ⟦Δ⟧)$)

$
  ⟦ctxwk(Γ, Δ)⟧ := ⟦tywk(Π Γ, Π Δ)⟧
$

#dntty($lbctxwk(ms("L"), ms("M"))$, $cal(C)_⊥(Σ ⟦ms("L")⟧, Σ ⟦ms("M")⟧)$)

$
  ⟦lbctxwk(ms("L"), ms("M"))⟧ := ⟦tywk(Σ ms("L"), Σ ms("M"))⟧
$

#dntty($hasty(Γ, a, A)$, $cal(C)(Π ⟦Γ⟧, ⟦A⟧)$)

#eqn-set(
  dntdef(r-var, $π_x$),
  dntdef(r-coe, $⟦hasty(Γ, a, A)⟧ ; ⟦tywk(A, A')⟧$),
)

#eqn-astack(
  dntdef(r-app, $Δ_(Π ⟦Γ⟧) ; Π⟦Γ⟧ ⊗ ⟦hasty(Γ, a, A)⟧ ; ⟦isfn(Γ, a, A, B)⟧$),
)

#eqn-set(
  dntdef(r-inj, $⟦hasty(Γ, a, A)⟧ ; α^+$),
  dntdef(r-proj, $⟦hasty(Γ, e, Π (fty(lb("f"), A)))⟧ ; π_lb("f")$),
  dntdef(r-tuple, $⟦istup(Γ, E, lb("T"))⟧$)
)

#eqn-astack(
  dntdef(r-cases, $Δ_(Π ⟦Γ⟧) 
    ; Π⟦Γ⟧ ⊗ ⟦hasty(Γ, e, Σ lb("L"))⟧ 
    ; idistl(Π ⟦Γ⟧, ⟦lb("L")⟧)
    ; ⟦isebrs(Γ, lb("L"), M, A)⟧
    $)
)

#todo[let]

#todo[iter]

#dntty($istup(Γ, E, lb("T"))$, $cal(C)(Π ⟦Γ⟧, Π ⟦lb("T")⟧)$)

#todo[nil-Π]

#todo[cons-Π]

#dntty($kebrs(cal(K), M, A)$, $cal(C)(Σ ⟦cal(K)⟧, A)$)

#todo[nil-Σ]

#todo[cons-Σ]

#todo[
  Definition: a $cal(V)$-enriched SSA model over a function space $ms("F")$
  w/ effect system $cal(E)$
]

#todo[
  GPT up some names for these...
]

#theorem(name: "Effect Soundness")[
  #todo[this]
]

#theorem(name: "Soundness of Substitution")[
  #todo[this]
]

#theorem(name: "Soundness")[
  #todo[this]
]

#theorem(name: "Completeness")[
  #todo[this]
]
