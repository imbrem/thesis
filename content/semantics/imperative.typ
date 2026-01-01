#import "../../syntax.typ": *
#import "../../todos.typ": *

#show: show-syntax

= Control-Flow Diagrams

#todo[regular categories are like _sequential control-flow_; objects are like state configurations]

#todo[coproducts allow us to have _branching control-flow_, including diamonds et al.]

#todo[
  Unstructured?
  - Don't draw associators
  - Flips are flips
  - So you can represent $N$ -- go find a citation for the $N$ trick
]

#todo[But... what about arbitrary CFGs? Namely, _loops_]

= Loops and Iterative Categories

#todo[pre-iterative category]

#todo[iterative category]

#todo[uniformity? need a good justification]

#todo[mark out subcategory $cal(K)$ of pure morphisms...]

#todo[we need _effects_ here...]

= Effects and Elgot Categories

#todo[
  introduce _effectful category_ w.r.t. effect system $cal(E)$ 
  -- _all_ effect systems are linear
]

#todo[
  Purity system as a special case: go find out a good name for this
]

#todo[uniformity w.r.t. effect system]

#todo[_directed_ uniformity]

= Premonoidal Categories

#definition(name: [$cal(V)$-Binoidal Category])[
  A $cal(V)$-binoidal category is a $cal(V)$-category equipped with
  - A function on objects $- ⊗ - ∈ |cal(C)| × |cal(C)| → |cal(C)|$
  - For each object $A ∈ |cal(C)|$, $cal(V)$-functors $A ⊗ -, - ⊗ A : cal(C) → cal(C)$ which
    agree with $- ⊗ -$ on objects

  In general, given $f: A_1 → B_1$ and $g : A_2 → B_2$, we define:
  - $f ⋉ g = f ⊗ A_2 ; B_1 ⊗ g : cal(C)(A_1 ⊗ A_2, B_1 ⊗ B_2)$
  - $f ⋊ g = A_1 ⊗ g ; f ⊗ B_2 : cal(C)(A_1 ⊗ A_2, B_1 ⊗ B_2)$

  We say that a morphism $f$ is _central_ if
  $
    ∀ A_2, B_2 ∈ |cal(C)|, ∀ g : cal(C)(A_2, B_2) . (f ⋉ g = f ⋊ g) ∧ (g ⋉ f = g ⋊ f)
  $
  In this case, we write
  $
    f ⊗ g := f ⋉ g = f ⋊ g
  $
  for the common value of $f ⋉ g$ and $f ⋊ g$.
]

#definition(name: [$cal(V)$-Premonoidal Category])[
  A $cal(V)$-premonoidal category is a $cal(V)$-binoidal category $cal(C)$
  equipped with
  - A distinguished _identity object_ $munit ∈ |cal(C)|$
  - Central natural isomorphisms:
    - $α_(A, B, C) : cal(C)((A ⊗ B) ⊗ C, A ⊗ (B ⊗ C))$ (the _associator_)
    - $λ_A : cal(C)(munit ⊗ A, A)$ (the _left unitor_)
    - $ρ_A : cal(C)(A ⊗ munit, A)$ (the _right unitor_)

  By natural, we mean that $α_(A, B, C)$. $λ_A$, and $ρ_A$ are natural in each of their components;
  i.e., for all morphisms $f: cal(C)(A, A')$, $g: cal(C)(B, B')$, and $h: cal(C)(C, C')$, the following
  _naturality squares_ hold:
  $
    (f ⊗ B) ⊗ C ; α_(A', B, C) & = α_(A, B, C) ; f ⊗ (g ⊗ h) //
                                           && : cal(C)((A ⊗ B) ⊗ C, A' ⊗ (B ⊗ C)) \
    A ⊗ (g ⊗ C) ; α_(A, B', C) & = α_(A, B, C) ; A ⊗ (g ⊗ h) //
                                           && : cal(C)((A ⊗ B) ⊗ C, A ⊗ (B' ⊗ C)) \
      A ⊗ B ⊗ h ; α_(A, B, C') & = α_(A, B, C) ; A ⊗ B ⊗ h //
                                           && : cal(C)((A ⊗ B) ⊗ C, A ⊗ (B ⊗ C')) \
            munit ⊗ f ; λ_(A') & = λ_A ; f && : cal(C)(munit ⊗ A, A') \
            f ⊗ munit ; ρ_(A') & = ρ_A ; f && : cal(C)(A ⊗ munit, A')
  $

  Such that the following coherence conditions hold:
  - (Pentagon Identity)
    For all objects $A, B, C, D ∈ |cal(C)|$, the following diagram commutes:
    $
      #diagram($
        //
        & (A ⊗ B) ⊗ (C ⊗ D) edge("dr", α_(A, B, (C ⊗ D)), ->)
        &\ ((A ⊗ B) ⊗ C) ⊗ D edge("ur", α_((A ⊗ B), C, D), ->) edge("d", α_(A, B, C) ⊗ D, ->)
        && A ⊗ (B ⊗ (C ⊗ D)) \
        (A ⊗ (B ⊗ C)) ⊗ D edge("rr", α_(A, B ⊗ C, D), ->) & & A ⊗ ((B ⊗ C) ⊗ D)
        edge("u", A ⊗ α_(B, C, D), ->)
      $)
    $

  - (Triangle Identity)
    For all objects $A, B ∈ |cal(C)|$, the following diagram commutes:
    $
      #diagram(cell-size: 15mm, $
        //
        (A ⊗ munit) ⊗ B edge(α_(A, munit, B), ->) edge("dr", ρ_A ⊗ id_B, ->, label-side: #right)
        & A ⊗ (munit ⊗ B) edge("d", id_A ⊗ λ_B, ->, label-side: #left) \
        & A ⊗ B
      $)
    $

    We say that a $cal(V)$-premonoidal category is _symmetric_ if it is equipped with an additional
    central natural isomorphism
    - $σ_(A, B) : cal(C)(A ⊗ B, B ⊗ A)$ (the _braiding_)

    Satisfying:
    - (Naturality): $∀ f : cal(C)(A, A') . f ⊗ B ; σ_(A', B) = σ_(A, B) ; B ⊗ f
      : cal(C)(A ⊗ B, B ⊗ A')$
    - (Symmetry): $σ_(A, B)^(-1) = σ_(B, A)$

    Such that the following coherence conditions hold:
    - (Hexagon Identity)
      For all objects $A, B, C ∈ |cal(C)|$, the following diagram commutes:
      $
        #diagram($ (A ⊗ B) ⊗ C edge(α_(A, B, C), ->) edge("d", σ_(A, B) ⊗ C, ->, label-side: #right) &
        A ⊗ (B ⊗ C) edge(σ_(A, B ⊗ C), ->, label-side: #left) &
        (B ⊗ C) ⊗ A edge("d", α_(B, C, A), ->, label-side: #left) \
        (B ⊗ A) ⊗ C edge(α_(B, A, C), ->, label-side: #right) &
        B ⊗ (A ⊗ C) edge(B ⊗ σ_(A, C), ->, label-side: #right) &
        B ⊗ (C ⊗ A) $)
      $
]

#definition(name: [Freyd Category])[
  #todo[this]
]

#definition(name: [$n$-ary Tensor Product])[
  Given a $cal(V)$-premonoidal category $cal(C)$...
  #todo[finish definition]
]

#todo[
  - In the literature, we have:
    - A Freyd category is a _choice_ of $cal(C)_⊥$
      - $cal(C)_⊥$ is structure for Freyd
      - Is property in the copy-discard / Markov worlds
    - _copy-discard_ categories, which are premonoidal + comonoids
      - These _induce_ a Freyd category
      - A morphism is _relevant_ if ...
      - A morphism is _affine_ if ...
      - What if I want to keep track of which morphisms are relevant/affine/central?
      - I need more structure
    - Effectful category
      - An effect system $cal(E)$ is just a bounded lattice with monotone functions
        is relevant, is affine, is central
      - An effectful category over an effect system $cal(E)$ maps effects to subcategories with
        $⊤$ to top
      - Morphisms between effect systems induce identity-on-objects functors
        between effectful categories
      - A Freyd category is just an effectful category over ${⊤, ⊥}$
      - A Cartesian category is just an effectful category over ${⊥}$
]

#todo[
  Introduce strong Elgot structure
]

= String Diagrams

#todo[monoidal categories and string diagrams]

#todo[iterative structure is a trace, see @hasegawa-02-trace]

#todo[state wire transform @roman-25-premonoidal]

#todo[namedrop RVSDG @reissmann-20-rvsdg; future work pointer]

#todo[
  namedrop Sea of Nodes
  @click-00-sea-of-nodes-thesis, @click-97-quads-to-graphs, @click-95-simple-graph;
  future work pointer
]

#context if (thesis-state.get)().is-standalone {
  the-bibliography
}
