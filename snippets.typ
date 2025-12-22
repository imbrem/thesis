/*
#todo[rewrite this]

We can think of a concrete category $cal(V)$ as "sets with extra structure":

- Each object $A ∈ |cal(V)|$ corresponds to a set $U A$; in particular,
  we will write $a ∈ A$ to mean $a ∈ U A$
- Each morphism $f : cal(V)(A, B)$ corresponds to a _unique_ function $U f : U A → U B$.

  In particular, since $U$ is faithful,
  we can ask whether an arbitrary function $g : U A → U B$
  "is a $cal(V)$-morphism from $A$ to $B$";
  i.e., whether there exists $f : cal(V)(A, B)$ such that $U f = g$.
  If there exists such an $f$, it is unique;
  hence, we can identify the morphisms $cal(V)(A, B)$
  with the subset of functions $U A → U B$ which "are $cal(V)(A, B)$ morphisms."

  In general, we will write such an $f$ if it exists as $U^(-1)_(cal(V)(A, B)) g$.

  We hence justify the further abuse of notation and write

  - $f : A → B$ to mean $U f : U A → U B$ where this would not cause confusion, and, in particular

  - Given $a ∈ A$, we define $f(a) ∈ B$ to mean $(U f)(a) ∈ U B$

As a concrete example, consider the category of partially-ordered sets and monotone functions $ms("Pos")$.
An object of $ms("Pos")$ is a partially-ordered set $(X, scripts(≤)_X)$,
and a morphism $f: (X, scripts(≤)_X) → (Y, scripts(≤)_Y)$ is a monotone function $f : X → Y$, i.e.
a function $f$ such that
$
  ∀ x_1, x_2 ∈ X . (x_1 scripts(≤)_X x_2) ==> (f(x_1) scripts(≤)_Y f(x_2))
$

We can directly equip $ms("Pos")$ with the structure of a concrete category by taking
$U(X, scripts(≤)_X) = X$ and $U f = f$.
Our abuse of notation is then precisely the usual mathematical convention of, for example,
specifying "a monotone function $f : ℕ → pset(X)$" without explicitly specifying that
$ℕ$ is ordered with the usual $≤$ relation on the naturals and
$pset(X)$ is ordered with the subset relation $⊆$.


Another particularly import example is the category of sets $cset$, which is trivially a
concrete category by taking $U$ to be the identity functor.
*/

/*
For the rest of this section, we will develop the theory of $cal(V)$-enriched categories in the
special case where $cal(V)$ is concretely cartesian. The general theory of enriched categories is
analogous, but much more complex since we need to deal with coherence conditions, however,
when $cal(V)$ is concretely cartesian, the definitions are essentially the same as in ordinary
category theory. In fact, we can recover the standard category theoretic definitions by noting that
a category is precisely a $cset$-enriched category.
*/


/*

== Compiling Between #iter-calc() and SSA

#todo[this]

=== Compiling #iter-calc() to SSA

#todo[this]

=== Compiling SSA to #iter-calc()

#todo[this]

== Dialects and Lowerings

#todo[expression-language hom w.r.t. refinement theory]

#todo[a _lowering_ is a refinement-preserving expression-language hom]

#todo[an _optimization_ is a refining endomorphism]

#todo[versus, an automorphism like the #iter-calc() equivalences...]

#todo[#iter-calc(expr2fun(iter-calc(ms("F")))) ≈ #iter-calc(ms("F"))]

*/
