// Verbatim mechanical transcription from:
// papers/isotope/denotational-semantics-of-ssa.tex
// Repository commit: afa82558acf643f53a3e038e635ed9520ace88c6
// Source section: Records and Enums through Environment Comonad, lines 5625–6596

#import "/lib/prelude.typ": *

= Records and Enums

#let paper-rule(label, ..lines) = prooftree(rule(label: msc(label), ..lines.pos()))

<apx:records-enums>
For simplicity, we defined our language to have only binary products and sums. However, we would like to support records (named $n$-ary products) and enums (named $n$-ary sums). We will implement these on top of our language using contexts; the resulting machinery will turn out to be crucial in proving the Böhm-Jacopini theorem in Appendix~#todo[Cross-reference: \@apx:data-control] and completeness in Section~#todo[Cross-reference: \@ssec:completeness.] We begin by defining #emph[packing] of variable contexts as follows: $ ⟨ dot.op ⟩ = upright(bold(1)) #h(2em) ⟨ Gamma   x : A ⟩ = ⟨ Gamma ⟩ ⊗ A $ While in general we destructure pairs using binary $sans("let")$-bindings, it will be more convenient to start defining operations on records in terms of projections. We begin by defining projections on pairs in the obvious manner: #align(center, grid(columns: (auto, auto), gutter: 2em,
  paper-rule($pi_l$, $Gamma tack.r_epsilon.alt e : A ⊗ B$, $Gamma tack.r_epsilon.alt pi_l e := sans("let") (x, y) = e; x : A$),
  paper-rule($pi_r$, $Gamma tack.r_epsilon.alt e : A ⊗ B$, $Gamma tack.r_epsilon.alt pi_r e := sans("let") (x, y) = e; y : A$),
)) We may then define projections on records as follows: $ pi_(( Delta   x : A )   y) #h(0em) e = pi_(Delta   y) ( pi_l #h(0em) e ) #h(2em) pi_(( Delta   x : A )   x) #h(0em) e = pi_r #h(0em) e $ with typing rule #align(center, paper-rule($pi_sans("rec")$, $Gamma tack.r_epsilon.alt e : ⟨Delta⟩$, $Delta(x) = A$, $Gamma tack.r_epsilon.alt pi_(Delta, x) e : A$)) We will omit $Delta$ when it is clear from context. We can define a term $Gamma tack.r_tack.t sans("packed") ( Gamma ) : \[ Gamma \]$ to "pack" up the current context into a record as follows: $ sans("packed") ( dot.op ) = ( ) #h(2em) sans("packed") ( Gamma   x : A ) = ( sans("packed") ( Gamma )   x ) $ We may now define packing and unpacking substitutions $sans("pack")_y^⊗ ( Gamma ) : Gamma mapsto y : ⟨ Gamma ⟩$, $sans("unpack")_y^⊗ ( Gamma ) : y : ⟨ Gamma ⟩ mapsto Gamma$ as follows: $ sans("pack")_y^⊗ ( Gamma ) = y mapsto sans("packed") ( Gamma ) #h(2em) sans("unpack")_y^⊗ ( Gamma ) = ( x mapsto pi_(Gamma   x) #h(0em) y )_(x in Gamma) $ Our equational theory is sufficient to show that the pack and unpack substitutions are inverses of each other: $ \[ sans("unpack")_y^⊗ ( Gamma ) \] sans("pack")_y^⊗ ( Gamma ) & approx sans("id")_Gamma : Gamma mapsto Gamma\
\[ sans("pack")_y^⊗ ( Gamma ) \] sans("unpack")_y^⊗ ( Gamma ) & approx sans("id")_(y : \[ Gamma \]) : y : Gamma mapsto y : Gamma $ Similarly, we may define a "packing" operation $⟨ dot.op ⟩$ on label-contexts as follows: $ ⟨ dot.op ⟩ = upright(bold(0)) #h(2em) ⟨ sans(L)   ell ( A ) ⟩ = ⟨ sans(L) ⟩ + A $ We may then define injections on enums as follows: $ iota_(( sans(L)   ell ( A ) )   kappa) #h(0em) e = iota_(sans(L)   kappa) ( iota_l #h(0em) e ) #h(2em) iota_(( sans(L)   ell ( A ) )   ell) #h(0em) e = iota_r #h(0em) e $ with typing rule #align(center, paper-rule($iota_sans("enum")$, $Gamma tack.r_epsilon.alt e : A$, $sans("L")(ell) = A$, $Gamma tack.r_epsilon.alt iota_(sans("L"), ell) e : ⟨sans("L")⟩$)) Similarly, we can define $n$-ary case-statements on enums by induction as follows: $ sans("case")_dot.op #h(0em) e #h(0em) { } & = oo\
sans("case")_(sans(L)   kappa ( A )) #h(0em) e #h(0em) { ( ell_i ( x_i ) : t_i )_i   kappa ( y ) : s } & = kw("case") med e #h(0em) { iota_l #h(0em) x : sans("case")_(sans(L)) #h(0em) x #h(0em) { ( ell_i ( A_i ) : t_i )_i }   iota_r #h(0em) y : s } $ with typing rule #align(center, paper-rule($sans("case")_sans("enum")$, $Gamma tack.r_epsilon.alt e : ⟦sans("L")⟧$, $forall i. Gamma, x_i : A_i tack.r t_i gt.tri sans("K")$, $Gamma tack.r sans("case")_(sans("L")) e { (ell_i(x_i) : t_i)_i } gt.tri sans("K")$)) where #align(center, paper-rule($oo$, $Gamma tack.r oo := sans("br") ell (); sans("where") ell(x) : { sans("br") ell x } gt.tri sans("L")$)) We may now define "packing" and "unpacking" label-substitutions $dot.op tack.r sans("pack")_kappa^(+) ( sans(L) ) : sans(L) arrow.r.squiggly kappa ( \[ sans(L) \] )$, $dot.op tack.r sans("unpack")_kappa^(+) ( sans(L) ) : kappa ( \[ sans(L) \] ) arrow.r.squiggly sans(L)$ as follows: $ sans("pack")_kappa^(+) ( dot.op ) = dot.op #h(2em) sans("pack")_kappa^(+) ( sans(L)   ell ( A ) ) = \[ kappa ( x ) mapsto sans("br") #h(0em) kappa #h(0em) iota_l #h(0em) x \] sans("pack")_kappa^(+) ( sans(L) )   ell ( x ) mapsto sans("br") #h(0em) kappa #h(0em) iota_r #h(0em) x $ $ sans("unpack")_kappa^(+) ( sans(L) ) = kappa ( x ) mapsto sans("unpack")^(+) ( sans(L) ) #h(0em) x $ where we have #align(center, paper-rule($sans("unpack")^+$, $Gamma tack.r_epsilon.alt e : sans("L")$, $Gamma tack.r sans("unpack")^+(sans("L")) e gt.tri sans("L")$)) defined as follows: $ sans("unpack")^(+) ( dot.op ) #h(0em) e = oo #h(2em) sans("unpack")^(+) ( sans(L)   ell ( A ) ) #h(0em) e = kw("case") med e #h(0em) { iota_l #h(0em) x : sans("unpack")^(+) ( sans(L) ) #h(0em) x   iota_r #h(0em) y : sans("br") #h(0em) ell #h(0em) y } $ We can further show that, in this case for all label contexts $sans(L)$, these substitutions are mutually inverse, i.e., that $ Gamma tack.r \[ sans("unpack")_kappa^(+) ( sans(L) ) \] sans("pack")_kappa^(+) ( sans(L) ) & approx sans("id")_(sans(L)) : sans(L) arrow.r.squiggly sans(L)\
Gamma tack.r \[ sans("pack")_kappa^(+) ( sans(L) ) \] sans("unpack")_kappa^(+) ( sans(L) ) & approx sans("id")_(kappa ( \[ sans(L) \] )) : kappa ( \[ sans(L) \] ) arrow.r.squiggly kappa ( \[ sans(L) \] ) $ Finally, fixing a distinguished variable $square.stroked.tiny$, it will be very useful to define a "#emph[variable packing]" operation on expressions and regions as follows: $ Gamma tack.r r gt.tri sans(L) ==> square.stroked.tiny : \[ Gamma \] tack.r ( ⟨ r ⟩^⊗ := \[ sans("unpack")_square.stroked.tiny^⊗ ( Gamma ) \] r ) gt.tri sans(L) $ In particular, for $Gamma$ pure, the packing operation $\[ dot.op \]$ is an injection on expressions and regions w.r.t. the equational theory, since $sans("unpack")_square.stroked.tiny^⊗ ( Gamma )$ has an inverse. Similarly, fixing a distinguished label $square.filled.medium$, we may define a "label packing" operation on regions as follows: $ Gamma tack.r r gt.tri sans(L) ==> Gamma tack.r ⟨ r ⟩^(+) := \[ sans("pack")_square.filled.medium^(+) ( sans(L) ) \] r gt.tri square.filled.medium ( \[ sans(L) \] ) $ Since the packing substitution has an inverse, it similarly follows that label packing is an injection w.r.t. the equational theory, i.e. $ Gamma tack.r r approx r' gt.tri sans(L) arrow.l.r.double Gamma tack.r ⟨ r ⟩^(+) approx ⟨ r' ⟩^(+) gt.tri sans(L) $ Finally, we can define a "packing" operation on regions to be given by label-packing followed by variable-packing, or vice versa (since it turns out the operations commute), as follows: $ Gamma tack.r r gt.tri sans(L) ==> square.stroked.tiny : \[ Gamma \] tack.r ⟨ r ⟩ := ⟨ ⟨ r ⟩^(+) ⟩^⊗ = ⟨ ⟨ r ⟩^⊗ ⟩^(+) gt.tri square.filled.medium ( sans(L) ) $ We similarly have that this is an injection for $Gamma$ pure, i.e. $ Gamma tack.r r approx r' gt.tri sans(L) arrow.l.r.double Gamma tack.r ⟨ r ⟩ approx ⟨ r' ⟩ gt.tri sans(L) $

= Böhm-Jacopini for SSA
<apx:data-control>
Now that we have given our equational theory, we want to show it is "good enough" to reason about the properties inherent to all SSA-based languages. In particular, we wish to show that we have enough power to reason about interconversion between data-flow and control-flow. For example, a state machine can be implemented either as a switch on a state value, or as a set of mutually-tail-recursive functions (i.e., the state can be encoded in the program counter). We demonstrate this by using some of the machinery from the previous section to state and prove a form of the Böhm-Jacopini theorem #todo[Resolve source reference `bohm-jacopini` during integration.] for SSA.

The Böhm-Jacopini theorem states that every general control-flow graph program can be rewritten to an equivalent program which uses only structured control-flow: i.e., it can be rewritten to a program using only conditional branching, sequencing, and loops. To adapt this result to SSA, we need to express branching, sequencing and loops as SSA regions $Gamma tack.r r gt.tri sans(L)$, so that we can build up an inductive set of structured regions. We will be maximally strict, and allow branching to an exit label in $sans(L)$ only as the terminal statement in a structured program (and, in particular, not from within a loop!). It is obvious that we can represent conditional branching using $sans("case")$-statements, but we need convenient primitives for sequencing and looping. Sequencing can be expressed using a $sans("where")$-block as follows (with $ell$ fresh): #align(center, paper-rule($sans("seq")$, $Gamma tack.r r gt.tri square.filled.medium(A)$, $Gamma, square.stroked.tiny : A tack.r s gt.tri sans("L")$, $Gamma tack.r sans("seq")(r, s) := ([square.filled.medium(x) mapsto sans("br") ell x] r; sans("where") ell(square.stroked.tiny) : {s}) gt.tri sans("L")$)) where “$square.stroked.tiny$" is a distinguished input variable, and "$square.filled.medium$" is a distinguished output label. Another, equivalent, way of writing sequencing is: $ Gamma tack.r sans("seq") ( r   s ) approx \[ square.filled.medium ( square.stroked.tiny ) mapsto s \] r gt.tri sans(L) $ That is, when we exit $r$, we jump to (a copy of) $s$.

Expressing structured looping is a bit more complicated, since we do not have mutable variables and hence cannot directly express while loops. If we recall that loops can be expressed as tail-recursive procedures which carry the loop state in the argument, then we can define a "functional do-while loop" as follows: #align(center, paper-rule($sans("loop")$, $Gamma tack.r_epsilon.alt e : A$, $Gamma, square.stroked.tiny : A tack.r r gt.tri square.filled.medium(B + A)$, $Gamma tack.r sans("loop")(e, r) := (sans("br") ell e; sans("where") ell(square.stroked.tiny) : { sans("seq")(r, sans("case") square.stroked.tiny { iota_l x : sans("br") square.filled.medium x, iota_r y : sans("br") ell y }) }) gt.tri square.filled.medium(B)$)) We can now define the inductive predicate $Gamma tack.r^(sans(s)) r gt.tri sans(L)$, which says that $r$ is a structured region with input variables $Gamma$ and output labels $sans(L)$, as in Figure~@fig:structured-regions. Note that this defines a subset of the well-typed regions: every region $r$ such that $Gamma tack.r^(sans(s)) r gt.tri sans(L)$ is also well-typed as $Gamma tack.r r gt.tri sans(L)$.

It now remains to give an algorithm to convert a region $r$ targeting label-context $sans(L)$ into an equivalent structured region $sans("WH")_(sans(L)) ( r )$. In particular, we define $ sans("WH")_(sans(L)) ( r ) = \[ sans("unpack")_square.filled.medium^(+) ( sans(L) ) \] sans("PW")_L ( r ) $ where we define $ sans("PW")_(sans(L)) ( sans("br") #h(0em) ell #h(0em) a ) & = sans("br") #h(0em) square.filled.medium #h(0em) iota_(sans(L)   ell) #h(0em) a\
sans("PW")_(sans(L)) ( kw("let") med x = a ; r ) & = kw("let") med x = a ; sans("PW")_(sans(L)) ( r )\
sans("PW")_(sans(L)) ( kw("let") med ( x   y ) = a ; r ) & = kw("let") med ( x   y ) = a ; sans("PW")_(sans(L)) ( r )\
sans("PW")_(sans(L)) ( kw("case") med e #h(0em) { iota_l #h(0em) x : r   iota_r #h(0em) y : s } ) & = kw("case") med e #h(0em) { iota_l #h(0em) x : sans("PW")_(sans(L)) ( r )   iota_r #h(0em) y : sans("PW")_(sans(L)) ( s ) }\
sans("PW")_(sans(L)) ( r med kw("where") med ( ell_i ( x_i ) : { t_i }   )_i ) & = sans("seq") ( sans("PW")_(sans(L)) ( r )   kw("case") med sans("ua") #h(0em) square.stroked.tiny #h(0em) { iota_l #h(0em) x : sans("br") #h(0em) square.filled.medium #h(0em) x\
 & #h(2em)   iota_r #h(0em) y : sans("loop") ( y   sans("case")_(sans(R)) #h(0em) square.stroked.tiny #h(0em) { ell_i ( x_i ) : sans("seq") ( sans("PW")_(sans(L)) ( t_i )   sans("br") #h(0em) square.filled.medium #h(0em) ( sans("ua") #h(0em) square.stroked.tiny ) } ) } )\
#h(2em) upright("where") #h(2em) sans(R) = ( ell_i ( A_i )   ) $ and $ sans("ua")_(sans(L)   dot.op) #h(0em) e = e #h(2em) sans("ua")_(sans(L)   ( sans(R)   ell ( A ) )) #h(0em) e = kw("case") med e #h(0em) { iota_l #h(0em) x : kw("case") med sans("ua")_(sans(L)   sans(R)) #h(0em) x #h(0em) { iota_l #h(0em) z : iota_l #h(0em) z   iota_r #h(0em) w : iota_r #h(0em) iota_l #h(0em) w }   iota_r #h(0em) y : iota_r #h(0em) ( iota_r #h(0em) y ) } $ Note that the base case $sans("PW")_(sans(L)) ( sans("br") #h(0em) ell #h(0em) a )$ is The $sans("PW")_(sans(L)) ( r )$ function does the actual transformation, and we can see that most of the cases are trivial except for:

- The base case, in which we simply replace a branch $sans("br") #h(0em) ell #h(0em) a$ with a branch to the output label $square.filled.medium$ with the appropriate injection $iota_(sans(L)   ell) #h(0em) a$ as parameter.

- The $r med kw("where") med ( ell_i ( x_i ) : { t_i }   )_i$ case, in which we replace the set of labels bound by the $sans("where")$ clause with a tag and a while loop containing a case statement branching on the tag. (This uses the $sans("ua")$ function, which implements associativity of $n$-ary coproducts. That is, given $Gamma tack.r_tack.t e : \[ L   R \]$, we have that $Gamma tack.r_tack.t sans("ua")_(sans(L)) #h(0em) e : \[ L \] + \[ R \]$.)

The Böhm-Jacopini theorem for SSA can then be written:

#block[
For all $Gamma tack.r r gt.tri sans(L)$, we have that $Gamma tack.r^(sans(s)) sans("WH")_(sans(L)) ( r ) gt.tri sans(L)$ is structured, and $Gamma tack.r r approx sans("WH")_(sans(L)) ( r ) gt.tri sans(L)$. In particular, we have that $Gamma tack.r^(sans(s)) sans("PW")_(sans(L)) ( r ) gt.tri square.filled.medium ( ⟨ sans(L) ⟩ )$ is structured, and $Gamma tack.r ⟨ r ⟩^(+) approx sans("PW")_r ( gt.tri ) square.filled.medium ( ⟨ sans(L) ⟩ )$.

]
#block[
#emph[Proof.] See Appendix~#todo[Cross-reference: \@proof:bohm-jacopini]~◻

]
#figure([#rule-set(
  paper-rule($sans("s-br")$, $Gamma tack.r_bot a : A$, $sans("L") ell = A$, $Gamma tack.r^sans("s") sans("br") ell a gt.tri sans("L")$),
  paper-rule($sans("s-let")_1-sans("r")$, $Gamma tack.r_epsilon.alt a : A$, $Gamma, x : A tack.r^sans("s") r gt.tri sans("L")$, $Gamma tack.r^sans("s") sans("let") x = a; r gt.tri sans("L")$),
  paper-rule($sans("s-let")_2-sans("r")$, $Gamma tack.r_epsilon.alt e : A ⊗ B$, $Gamma, x : A, y : B tack.r^sans("s") r gt.tri sans("L")$, $Gamma tack.r^sans("s") sans("let") (x, y) = e; r gt.tri sans("L")$),
  paper-rule($sans("s-case-r")$, $Gamma tack.r_epsilon.alt e : A + B$, $Gamma, x : A tack.r^sans("s") r gt.tri sans("L")$, $Gamma, y : B tack.r^sans("s") s gt.tri sans("L")$, $Gamma tack.r^sans("s") sans("case") e { iota_l x : r, iota_r y : s } gt.tri sans("L")$),
  paper-rule($sans("s-seq")$, $Gamma tack.r^sans("s") r gt.tri square.filled.medium(A)$, $Gamma, square.stroked.tiny : A tack.r^sans("s") s gt.tri sans("L")$, $Gamma tack.r^sans("s") sans("seq")(r, s) gt.tri sans("L")$),
  paper-rule($sans("s-loop")$, $Gamma tack.r_epsilon.alt e : square.filled.medium(A)$, $Gamma, square.stroked.tiny : A tack.r^sans("s") r gt.tri square.filled.medium(B + A)$, $Gamma tack.r^sans("s") sans("loop")(e, r) gt.tri square.filled.medium(B)$),
)

  ],
  caption: [
    Typing rules for structured regions
  ]
)
<fig:structured-regions>

= The Environment Comonad
<apx:environment>
If $cal(C)$ is a Freyd category, then given an object $R in bar.v cal(C) bar.v$, the functor $R ⊗ dot.op$ is a comonad with counit $pi_r : R ⊗ A arrow.r A$ and comultiplication $Delta_R ⊗ A ; alpha : R ⊗ A arrow.r R ⊗ ( R ⊗ A )$, often called the #emph[environment comonad] or #emph[coreader comonad]. In $sans("Set")$, the co-Kleisli category of $R ⊗ dot.op$ is isomorphic to the Kleisli category of the reader monad $R arrow.r dot.op$, and thus can be equipped with the structure of a distributive Elgot category. We might therefore intuit that, in general, if $cal(C)$ is a distributive Elgot category, the co-Kleisli category of $R ⊗ dot.op$ has this structure, even if e.g. $cal(C)$ lacks exponentials. The rest of this section is dedicated to proving this, which, beyond providing yet another class of $lambda_(sans("SSA"))$ models, will also give us a some useful equations and notation to use in our proofs later in the appendix. We begin by giving an explicit definition:

#block[
Given a Freyd category $cal(C)$ and an object (the #emph[environment]) $R in bar.v cal(C) bar.v$, the #emph[environment comonad] $cal(C)_(R ⊗ dot.op)$ is given by the functor $A mapsto R ⊗ A$ and has counit $pi_r$ and comultiplication $Delta_R ⊗ A$. It follows that composition of co-Kleisli morphisms $f : R ⊗ A arrow.r B$, $g : R ⊗ B arrow.r C$ is given by $ f gt.double_R g := Delta_R ; alpha ; R ⊗ f ; g : R ⊗ A arrow.r C $ In particular, we can define an identity on objects functor $sans("env")_R : cal(C) arrow.r cal(C)_(R ⊗ dot.op)$ as follows: $ sans("env")_R ( f ) := pi_r ; f $ Where it is clear from context, we will leave out the environment $R$.

]
Given $f : R ⊗ A arrow.r B$, we will introduce the syntax sugar $ sans("rlet") ( f ) := Delta_R ; alpha ; R ⊗ f : R ⊗ A arrow.r R ⊗ B $ In particular, we have that $f gt.double_() g = sans("rlet") ( f ) ; g$ and $sans("rlet") ( sans("env")_() ( f ) ) := R ⊗ f$. It is trivial to verify (for example, by drawing string diagrams) that $ sans("rlet") ( sans("rlet") ( f ) ; g ) = sans("rlet") ( f ) ; sans("rlet") ( g ) ==> f gt.double_() ( g gt.double_() h ) = ( f gt.double_() g ) gt.double_() h\
sans("rlet") ( f ) ; pi_r = f ==> f gt.double_() pi_r = f #h(2em) sans("rlet") ( pi_r ) = sans("id") ==> pi_r gt.double_() f = f $ and hence that $cal(C)_(R ⊗ dot.op)$ is indeed a category. To show it is in fact a #emph[Freyd category], we can define tensor functors $ f ⊗_R X & := alpha^(- 1) ; f ⊗ X : R ⊗ ( A ⊗ X ) arrow.r B ⊗ X\
X ⊗_R f & := R ⊗ sigma ; f ⊗_R X ; sigma : R ⊗ ( X ⊗ A ) arrow.r X ⊗ B $ We can define

- Associators $alpha_(A   B   C)^R := sans("env")_R ( alpha_(A   B   C) )$

- Unitors $lambda_A^R := sans("env")_R ( lambda_A )$ and $rho_A^R := sans("env")_R ( rho_A )$

- Symmetries $sigma_(A   B)^R := sans("env")_R ( sigma_(A   B) )$

- Projections $pi_l^R := sans("env")_R ( pi_l )$ and $pi_r^R := sans("env")_R ( pi_r )$

- Terminal morphisms $!_A^R := sans("env")_R ( !_A ) = !_(R ⊗ A)$

- Diagonals $Delta_A^R := sans("env")_R ( Delta_A )$

- Pure morphisms $cal(C)_(R ⊗ dot.op)_tack.t ( A   B ) = cal(C)_tack.t ( R ⊗ A   B )$

#block[
We can always equip $cal(C)_(R ⊗ dot.op)$ with the structure of a Freyd category as described above ; furthermore, $sans("env")_R ( dot.op )$ strictly preserves premonoidal structure.

]
#block[
#emph[Proof.] We have that $ sans("env")_R ( f ⊗ A ) & = pi_r ; f ⊗ A = alpha^(- 1) ; ( pi_r ; f ) ⊗ A = sans("env")_R ( f ) ⊗_R A\
sans("env")_R ( A ⊗ f ) & = pi_r ; A ⊗ f = R ⊗ sigma ; alpha^(- 1) ; ( pi_r ; f ) ⊗ A ; sigma = A ⊗_R sans("env")_R ( f ) $ and hence that $sans("env")_R$ preserves products. Since $sans("env")_R$ is a functor, to check we indeed have a Freyd category, it suffices to show that:

- $alpha_(A   B   C)^R$ is natural: we have that, given $f : R ⊗ A arrow.r A'$, $g : R ⊗ B arrow.r B'$, $h : R ⊗ C arrow.r C'$ $ ( f ⊗_R B ) ⊗_R C gt.double_() alpha_(A'   B   C) & = alpha_(A   B   C) gt.double_() f ⊗_R ( B ⊗ C )\
  ( A ⊗_R g ) ⊗ C gt.double_() alpha_(A   B'   C) & = alpha_(A   B   C) gt.double_() A ⊗_R ( g ⊗_R C )\
  ( A ⊗ B ) ⊗_R h gt.double_() alpha_(A   B   C') & = alpha_(A   B   C) gt.double_() A ⊗_R ( B ⊗_R h )\
   $<eqn:env-a-nat-1> since, for each equation, both sides are equal to the same string diagram in Figure~@fig:env-a-nat-1, @fig:env-a-nat-2, and @fig:env-a-nat-3 respectively.

- $lambda_A^R$ is natural: we have that, for $f : R ⊗ A arrow.r A'$, $ f ⊗_R upright(bold(1)) gt.double_() lambda_(A')^R & = Delta_R ; alpha ; R ⊗ ( alpha^(- 1) ; f ⊗ upright(bold(1)) ) ; pi_r ; pi_l\
   & = R ⊗ pi_l ; f\
   & = Delta_R ; alpha ; R ⊗ ( pi_r ; pi_l ) ; f & = lambda_A^R gt.double_() f $ In general, we note that, for all $g : R ⊗ A arrow.r A' ⊗ upright(bold(1))$, $g gt.double_() lambda^R = g ; pi_l$.

- $rho_A^R$ is natural: $ upright(bold(1)) ⊗_R f gt.double_() rho_(A')^R & = Delta_R ⊗ ( upright(bold(1)) ⊗ A ) ; alpha ; R ⊗ ( R ⊗ sigma ; alpha^(- 1) ; f ⊗ upright(bold(1)) ; sigma ) ; pi_r ; pi_r\
   & = R ⊗ pi_r ; f\
   & = Delta_R ; alpha ; R ⊗ ( pi_r ; pi_r ) ; f & = rho_A^R gt.double_() f $ In general, we note that, for all $g : R ⊗ A arrow.r upright(bold(1)) ⊗ A'$, $g gt.double_() rho^R = g ; pi_r$.

- $sigma_(A   B)^R$ is natural: given $f : R ⊗ A arrow.r A'$ and $g : R ⊗ B arrow.r B'$, we have that $ f ⊗_R B gt.double_() sigma_(A'   B)^R & = Delta_R ⊗ ( A ⊗ B ) ; alpha ; R ⊗ ( alpha^(- 1) ; f ⊗ B ) ; pi_r ; sigma\
   & = alpha^(- 1) ; f ⊗ B ; sigma\
   & = R ⊗ sigma ; R ⊗ sigma ; f ⊗ B ; sigma\
   & = Delta_R ⊗ ( B ⊗ A ) ; R ⊗ ( pi_r ; sigma ) ; R ⊗ sigma ; alpha^(- 1) ; f ⊗ B ; sigma & = sigma_(A   B)^R gt.double_() B ⊗_R f $ and $ A ⊗ g gt.double_() sigma_(A, B\x27)^R
  &= Delta_R ⊗ (A ⊗ B); alpha; R ⊗ (R ⊗ sigma; alpha^(-1); g ⊗ A; sigma); pi_r; sigma \
  &= R ⊗ sigma; alpha^(-1); g ⊗ A; cancel((sigma; sigma)) \
  &= Delta_R ⊗ (A ⊗ B); alpha; R ⊗ (pi_r; sigma); alpha^(-1); g ⊗ A \
  &= sigma_(A, B)^R gt.double_() g ⊗_R A $

- Pure morphisms are central: given $f : R ⊗ A arrow.r A'$ and $g : R ⊗ B arrow.r B'$ pure, we have that $ f ⊗_R B gt.double_() A' ⊗_R g & = Delta_R ; alpha ; R ⊗ ( alpha^(- 1) ; f ⊗ B ; sigma ) ; alpha^(- 1) ; g ⊗ A' ; sigma\
   & = Delta_R ; alpha ; R ⊗ ( R ⊗ sigma ; alpha^(- 1) ; g ⊗ A ; sigma ) ; alpha^(- 1) ; f ⊗ B'\
   & = A ⊗_R g gt.double_() f ⊗_R B' $ since both sides correspond to the diagram in Figure~@fig:env-slide. We will write this as $f ⊗_R g$.

- $!_A^R$ is terminal for pure morphisms: yes, since $!_A^R$ is just $!_(R ⊗ A)$ which is terminal in $cal(C)$

- $Delta_A^R$ duplicates pure morphisms: we have $ f gt.double_() Delta_B^R & = Delta_R ; alpha ; R ⊗ f ; pi_r ; Delta_(A')\
   & = f ; Delta_(A') = Delta_(R ⊗ A) ; f ⊗ f\
   & = Delta_R ; alpha ; R ⊗ ( alpha^(- 1) ; f ⊗ A' ) ; R ⊗ sigma ; alpha^(- 1) ; f ⊗ A' ; sigma & = Delta_A^R gt.double_() f ⊗_R f $

~◻

]
#figure([#figure(environment-naturality-diagram(0),
    caption: [
      Equation~#todo[Cross-reference: \@eqn:env-a-nat-1]
    ]
  )
  <fig:env-a-nat-1>

  #figure(environment-naturality-diagram(1),
    caption: [
      Equation~#todo[Cross-reference: \@eqn:env-a-nat-2]
    ]
  )
  <fig:env-a-nat-2>

  #figure(environment-naturality-diagram(2),
    caption: [
      Equation~#todo[Cross-reference: \@eqn:env-a-nat-3]
    ]
  )
  <fig:env-a-nat-3>

  ],
  caption: [
    Naturality of the associator in the co-Kleisli category of the environment comonad
  ]
)
<fig:env-a-nat>

#figure(environment-centrality-diagram(),
  caption: [
    Centrality of pure morphisms in the environment comonad's co-Kleisli category
  ]
)
<fig:env-slide>

Now, assume $cal(C)$ is distributive. We wish to show that $A + B$ is a coproduct in $cal(C)_(R ⊗ dot.op)$, and furthermore that $cal(C)_(R ⊗ dot.op)$ is distributive; note that even the former may not be the case without distributivity! We proceed as follows:

#block[
If $cal(C)$ is a distributive Freyd category, then $cal(C)_(R ⊗ dot.op)$ is also distributive Freyd

]
#block[
#emph[Proof.] Given $f : R ⊗ A arrow.r B$ and $g : R ⊗ A arrow.r C$, we may define the coproduct and injections $ \[ f   g \]_R := delta^(- 1) ; \[ f   g \] : R ⊗ A arrow.r B + C #h(2em) iota_l^R := pi_r ; iota_r : R ⊗ A arrow.r A + B #h(2em) iota_r^R := pi_r ; iota_r : R ⊗ B arrow.r A + B $ To verify this is indeed a coproduct, we can check that $ iota_l^R gt.double_() \[ f   g \]_R & = Delta_R ; alpha ; R ⊗ ( pi_r ; iota_r ) ; delta^(- 1) ; \[ f   g \] = R ⊗ iota_r ; delta^(- 1) ; \[ f   g \] = f\
iota_r^R gt.double_() \[ f   g \]_R & = Delta_R ; alpha ; R ⊗ ( pi_r ; iota_l ) ; delta^(- 1) ; \[ f   g \] = R ⊗ iota_l ; delta^(- 1) ; \[ f   g \] = g $ This morphism is obviously unique, since we have for all $h : R ⊗ ( A + B ) arrow.r C$ $ [iota_l^R gt.double_() h, iota_r^R gt.double_() h]_R
  = delta^(-1); [Delta_R; alpha; R ⊗ iota_l; pi_r; h, Delta_R; alpha; R ⊗ iota_r; pi_r; h]
  = cancel((delta^(-1); [R ⊗ iota_r, R ⊗ iota_l])); h $ To show that $R_(cal(C) ⊗ dot.op)$ is indeed distributive, we need $delta^(R - 1) := sans("env")_R ( delta^(- 1) ) = pi_r ; delta^R$ to be the inverse to $delta^R := \[ A ⊗ iota_l^R   A ⊗ iota_r^R \]_R$, which can easily be derived from the functoriality of $sans("env")_R ( dot.op )$, since $ sans("env")_R ( delta ) = pi_r ; \[ iota_l ; iota_r \] = delta^(- 1) ; \[ pi_r ; iota_l   pi_r iota_r \] = delta^R $~◻

]
Note in particular that this allows us to define sums $ f +_R g & = \[ f gt.double_() iota_l^R   g gt.double_() iota_r^R \]_R\
 & = delta^(- 1) ; \[ Delta_R ⊗ ( A + B ) ; alpha ; R ⊗ f ; pi_r ; iota_l   Delta_R ⊗ ( A + B ) ; alpha ; R ⊗ g ; pi_r ; iota_r \] & = delta^(- 1) ; f + g $ Our final task is to show that, if $cal(C)$ is a strong Elgot category, then so is $R_(cal(C) ⊗ dot.op)$, and, in particular, with fixpoint operator $sans("rfix") ( f )$. Note that, just like we needed distributivity to have coproducts at all, we will need strength to have an Elgot structure. We begin by stating some generally useful properties of $sans("rcase") ( f )$ and $sans("rfix") ( f )$. In particular, we have that: For $f : R ⊗ A arrow.r B + C$:

- Given $h : R ⊗ X arrow.r A$, we have $ sans("rlet") ( h ) ; sans("rcase") ( f ) & = Delta_R ⊗ X ; alpha ; R ⊗ h ; Delta_R ⊗ A ; alpha ; R ⊗ f ; delta^(- 1)\
   & = Delta_R ⊗ X ; alpha ; R ⊗ ( Delta_R ⊗ X ; alpha ; R ⊗ h ; f ) ; delta^(- 1)\
   & = sans("rcase") ( sans("rlet") ( h ) ; f ) & = sans("rcase") ( h gt.double_() f ) $

- Given $g : R ⊗ B arrow.r X$, $h : R ⊗ C arrow.r Y$, we have $ sans("rcase") ( f gt.double_() g +_R h ) & = sans("rlet") ( f gt.double_() g +_R h ) ; delta^(- 1)\
   & = sans("rlet") ( f ) ; sans("rlet") ( g +_R h ) ; delta^(- 1)\
   & = sans("rlet") ( f ) ; Delta_R ⊗ ( B + C ) ; alpha ; R ⊗ ( delta^(- 1) ; g + h ) ; delta^(- 1)\
   & = sans("rlet") ( f ) ; Delta_R ⊗ ( B + C ) ; alpha ; R ⊗ delta^(- 1) ; delta^(- 1) ; ( R ⊗ g ) + ( R ⊗ h )\
   & = sans("rlet") ( f ) ; delta^(- 1) ; sans("rlet") ( g ) + sans("rlet") ( h )\
   & = sans("rcase") ( f ) ; sans("rlet") ( g ) + sans("rlet") ( h )\
   & = sans("rlet") ( f ) ; sans("rlet") ( g ) +_R sans("rlet") ( h ) $

Similarly, for $f : R ⊗ A arrow.r B + A$:

- Given $h : R' arrow.r_tack.t R$, $h ⊗ A ; sans("rfix") ( f ) = sans("rfix") ( h ⊗ A ; f )$: we have that $ h ⊗ A ; sans("rcase") ( f ) & = h ⊗ A ; Delta_R ⊗ A ; alpha ; R ⊗ f ; delta^(- 1)\
   & = Delta_(R') ⊗ A ; alpha ; h ⊗ ( h ⊗ A ; f ) ; delta^(- 1)\
   & = Delta_(R') ⊗ A ; alpha ; R ⊗ ( h ⊗ A ; f ) ; delta^(- 1) ; h ⊗ B + h ⊗ A\
   & = sans("rcase") ( h ⊗ A ; f ) ; h ⊗ B + h ⊗ A $ and hence by uniformity that $ h ⊗ A ; sans("rfix") ( f ) & = h ⊗ A ; ( sans("rcase") ( f ) )^dagger ; pi_r\
   & = ( sans("rcase") ( h ⊗ A ; f ) ; h ⊗ B + R' ⊗ A )^dagger ; pi_r\
   & = ( sans("rcase") ( h ⊗ A ; f ) )^dagger ; h ⊗ B ; pi_r & = sans("rfix") ( h ⊗ A ; f ) $

- $sans("rlet") ( sans("rfix") ( f ) ) = ( sans("rcase") ( f ) )^dagger$: we have that $  & ( Delta_R ⊗ A ; alpha ) ; ( R ⊗ sans("rcase") ( f ) ; delta^(- 1) ; R ⊗ pi_r + R ⊗ ( R ⊗ A ) )\
   & = Delta_R ⊗ A ; alpha ; R ⊗ ( sans("let") ( f ) ; pi_l ⊗ ( B + A ) ; delta^(- 1) ) ; delta^(- 1) ; R ⊗ pi_r + R ⊗ ( R ⊗ A )\
   & = Delta_R ⊗ A ; alpha ; R ⊗ f ; Delta_R ⊗ ( B + A ) ; alpha ; R ⊗ delta^(- 1) ; delta^(- 1) ; R ⊗ pi_r + R ⊗ ( R ⊗ A )\
   & = Delta_R ⊗ A ; alpha ; R ⊗ f ; delta^(- 1) ; ( Delta_R ⊗ A ; alpha ; R ⊗ pi_r ) + ( Delta_R ⊗ A ; alpha )\
   & = Delta_(R ⊗ A) ; ( R ⊗ A ) ⊗ f ; pi_l ⊗ ( B + A ) ; delta^(- 1) ; R ⊗ A + ( Delta_R ⊗ A ; alpha )\
   & = sans("rcase") ( f ) ; R ⊗ A + ( Delta_R ⊗ A ; alpha ) $ It follows by uniformity and strength that $ sans("rlet") ( sans("rfix") ( f ) ) = sans("let") ( sans("rfix") ( f ) ) ; pi_l ⊗ B & = Delta_(R ⊗ A) ; ( R ⊗ A ) ⊗ sans("rfix") ( f ) ; pi_l ⊗ B\
   & = Delta_R ⊗ A ; alpha ; R ⊗ sans("rfix") ( f )\
   & = Delta_R ⊗ A ; alpha ; R ⊗ ( ( sans("rcase") ( f ) )^dagger ; pi_r )\
   & = Delta_R ⊗ A ; alpha ; ( R ⊗ sans("rcase") ( f ) ; delta^(- 1) ; R ⊗ pi_r + R ⊗ ( R ⊗ A ) )^dagger\
   & = ( sans("rcase") ( f ) )^dagger $ as desired.

We also state some generally useful properties of $sans("rlet") ( f )$:

- For all $f : R ⊗ A arrow.r C$, $g : R ⊗ B arrow.r C$, $ sans("rlet") ( delta^(- 1) ; \[ f   g \] ) & = Delta_R ⊗ ( A + B ) ; alpha ; R ⊗ ( delta^(- 1) ; \[ f   g \] )\
   & = delta^(- 1) ; \[ Delta_R ⊗ A ; alpha ; f   Delta_R ⊗ B ; alpha ; g \]\
   & = delta^(- 1) ; \[ sans("rlet") ( f )   sans("rlet") ( g ) \] $

We may now state our desired result as follows:

#block[
If $cal(C)$ is a premonoidal strong Elgot category, then so is $cal(C)_(R ⊗ dot.op)$ with fixpoint operator $sans("rfix") ( f )$.

]
#block[
#emph[Proof.] We check each of the Elgot axioms as follows:

- #emph[Fixpoint:] given $f : R ⊗ A arrow.r B + A$, we have that $ sans("rfix") ( f ) & = ( sans("rcase") ( f ) )^dagger ; pi_r = ( sans("rlet") ( f ) ; delta^(- 1) )^dagger ; pi_r\
   & = sans("rlet") ( f ) ; delta^(- 1) ; \[ sans("id")_(R ⊗ B)   ( sans("rlet") ( f ) ; delta^(- 1) )^dagger \] ; pi_r\
   & = sans("rlet") ( f ) ; delta^(- 1) ; \[ pi_r   ( sans("rcase") ( f ) )^dagger ; pi_r \] & = f gt.double_() \[ pi_r   sans("rfix") ( f ) \]_R $ as desired.

- #emph[Naturality:] given $f : R ⊗ A arrow.r B + A$, $g : R ⊗ B arrow.r C$, we have that $ sans("rfix") ( f gt.double_() g +_R A ) & = ( sans("rlet") ( Delta_R ⊗ A ; alpha ; R ⊗ f ; delta^(- 1) ; g + pi_r ) ; delta^(- 1) )^dagger ; pi_r\
   & = ( sans("rlet") ( Delta_R ⊗ A ; alpha ; R ⊗ f ; delta^(- 1) ) ; delta^(- 1) ; R ⊗ g + R ⊗ pi_r )^dagger ; pi_r\
   & = ( Delta_R ⊗ A ; alpha ; R ⊗ ( Delta_R ⊗ A ; alpha ; R ⊗ f ; delta^(- 1) ) ; delta^(- 1) ; ( pi_r ; g ) + R ⊗ pi_r )^dagger\
   & = ( Delta_R ⊗ A ; alpha ; R ⊗ f ; delta^(- 1) ; ( Delta_R ⊗ B ; alpha ; pi_r ; g ) + ( Delta_R ⊗ A ; alpha ; R ⊗ pi_r ) )^dagger\
   & = ( Delta_R ⊗ A ; alpha ; R ⊗ f ; delta^(- 1) ; g + R ⊗ A )^dagger\
   & = ( Delta_R ⊗ A ; alpha ; R ⊗ f ; delta^(- 1) )^dagger ; g = ( sans("rcase") ( f ) )^dagger ; g $ On the other hand, we have that $ sans("rfix") ( f ) gt.double_() g & = Delta_R ⊗ A ; alpha ; R ⊗ ( sans("rcase") ( f ) ; pi_r + R ⊗ A )^dagger ; g\
   & = Delta_R ⊗ A ; alpha ; ( R ⊗ ( sans("rcase") ( f ) ; pi_r + R ⊗ A ) ; delta^(- 1) )^dagger ; g\
   & = Delta_R ⊗ A ; alpha ; ( R ⊗ ( Delta_R ⊗ A ; alpha ; R ⊗ f ; delta^(- 1) ; pi_r + R ⊗ A ) ; delta^(- 1) )^dagger ; g\
   & = Delta_R ⊗ A ; alpha ; ( R ⊗ ( Delta_R ⊗ A ; alpha ; R ⊗ f ; delta^(- 1) ) ; delta^(- 1) ; R ⊗ pi_r + R ⊗ ( R ⊗ A ) )^dagger ; g $ By uniformity, it hence suffices to show that $  & ( Delta_R ⊗ A ; alpha ) ; ( R ⊗ ( Delta_R ⊗ A ; alpha ; R ⊗ f ; delta^(- 1) ) ; delta^(- 1) ; R ⊗ pi_r + R ⊗ ( R ⊗ A ) )\
   & = Delta_R ⊗ A ; alpha ; R ⊗ f ; delta^(- 1) ; ( Delta_R ⊗ B ; alpha ; R ⊗ pi_r ) + ( Delta_R ⊗ A ; alpha )\
   & = sans("rcase") ( f ) ; ( R ⊗ B ) + ( Delta_R ⊗ A ; alpha ) $ to yield the desired result.

- #emph[Codiagonal:] given $f : R ⊗ A arrow.r ( B + A ) + A$, we have $  & sans("rfix") ( sans("rfix") ( f ) )\
   & = ( Delta_R ⊗ A ; alpha med ; R ⊗ ( ( sans("rcase") ( f ) )^dagger ; pi_r ) ; delta^(- 1) )^dagger ; pi_r\
   & = ( Delta_R ⊗ A ; alpha ; R ⊗ ( sans("rcase") ( f ) ; pi_r + R ⊗ A )^dagger ; delta^(- 1) )^dagger ; pi_r\
   & = ( Delta_R ⊗ A ; alpha ; ( R ⊗ ( sans("rcase") ( f ) ; pi_r + R ⊗ A ) ; delta^(- 1) )^dagger ; delta^(- 1) )^dagger ; pi_r\
   & = ( Delta_R ⊗ A ; alpha ; ( R ⊗ ( sans("rcase") ( f ) ; pi_r + R ⊗ A ) ; delta^(- 1) ; delta^(- 1) + R ⊗ ( R ⊗ A ) )^dagger )^dagger ; pi_r\
   & = ( Delta_R ⊗ A ; alpha ; ( R ⊗ ( sans("rcase") ( f ) ; pi_r + R ⊗ A ) ; delta^(- 1) ; delta^(- 1) + R ⊗ ( R ⊗ A ) )^dagger ; pi_r + R ⊗ A )^dagger\
   & = ( Delta_R ⊗ A ; alpha ; ( R ⊗ ( sans("rcase") ( f ) ; pi_r + R ⊗ A ) ; delta^(- 1) ; ( delta^(- 1) ; ( pi_r + R ⊗ A ) ) + R ⊗ ( R ⊗ A ) )^dagger )^dagger $ On the other hand, we have $ sans("rfix") ( f gt.double_() \[ pi_r   iota_l^R \]_R ) & = sans("rfix") ( Delta_R ⊗ A ; alpha ; R ⊗ f ; delta^(- 1) ; \[ pi_r   pi_r ; iota_l \] )\
   & = sans("rfix") ( f ; \[ sans("id")   iota_l \] )\
   & = ( Delta_R ⊗ A ; alpha ; R ⊗ ( f ; \[ sans("id")   iota_l \] ) ; delta^(- 1) )^dagger ; pi_r\
   & = ( Delta_R ⊗ A ; alpha ; R ⊗ f ; delta^(- 1) ; delta^(- 1) + R ⊗ A ; \[ sans("id")   iota_l \] )^dagger ; pi_r\
   & = ( ( Delta_R ⊗ A ; alpha ; R ⊗ f ; delta^(- 1) ; delta^(- 1) + R ⊗ A )^dagger )^dagger ; pi_r\
   & = ( ( Delta_R ⊗ A ; alpha ; R ⊗ f ; delta^(- 1) ; delta^(- 1) + R ⊗ A )^dagger ; pi_r + R ⊗ A )^dagger\
   & = ( ( Delta_R ⊗ A ; alpha ; R ⊗ f ; delta^(- 1) ; delta^(- 1) + R ⊗ A ; ( pi_r + R ⊗ A ) + R ⊗ A )^dagger )^dagger\
   $ By uniformity, it therefore suffices to show that $  & ( Delta_R ⊗ A ; alpha ) ; ( R ⊗ ( sans("rcase") ( f ) ; pi_r + R ⊗ A ) ; delta^(- 1) ; ( delta^(- 1) ; ( pi_r + R ⊗ A ) ) + R ⊗ ( R ⊗ A ) )\
   & = Delta_R ⊗ A ; alpha ; R ⊗ ( Delta_R ⊗ A ; alpha ; R ⊗ f ; delta^(- 1) ; pi_r + R ⊗ A ) ; delta^(- 1) ; ( delta^(- 1) ; ( pi_r + R ⊗ A ) ) + R ⊗ ( R ⊗ A )\
   & = Delta_R ⊗ A ; alpha ; R ⊗ ( Delta_R ⊗ A ; alpha ; R ⊗ f ; delta^(- 1) ) ;\
   & #h(2em) delta^(- 1) ; R ⊗ pi_r + R ⊗ ( R ⊗ A ) ; ( delta^(- 1) ; ( pi_r + R ⊗ A ) ) + R ⊗ ( R ⊗ A )\
   & = Delta_R ⊗ A ; alpha ; R ⊗ f ; delta^(- 1) ; delta^(- 1) + ( R ⊗ A ) ; ( pi_r + R ⊗ A ) + ( Delta_R ⊗ A ; alpha ) $ to obtain the desired result.

- #emph[Uniformity:] Given $f : R ⊗ A arrow.r B + A$, $g : R ⊗ X arrow.r B + X$ and $h : R ⊗ X arrow.r_tack.t A$ such that $h gt.double_() f = g gt.double_() B +_R h$, we have that $ sans("rlet") ( h ) ; sans("rcase") ( f ) & = sans("rcase") ( h gt.double_() f )\
   & = sans("rcase") ( g gt.double_() B +_R h )\
   & = sans("rcase") ( g ) ; ( R ⊗ B ) + sans("rlet") ( h ) $ and hence by uniformity that $ h gt.double_() sans("rfix") ( f ) = sans("rlet") ( h ) ; ( sans("rcase") ( f ) )^dagger ; pi_r = ( sans("rcase") ( g ) )^dagger ; pi_r = sans("rfix") ( g ) $

~◻

]
