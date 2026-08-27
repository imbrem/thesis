// Native Typst presentation of the λ_SSA typing infrastructure.

#import "/lib/prelude.typ": *

#let inst-set(effect, a, b) = $cal(I)_#effect (#a, #b)$
#let label-ctx = $sans("L")$
#let label-ctx2 = $sans("K")$

#let expr-var = rule(
  label: msc("var"),
  $Gamma(x) = A$,
  eff-typing($Gamma$, $epsilon$, $x$, $A$),
)
#let expr-op = rule(
  label: msc("op"),
  $f in #inst-set($epsilon$, $A$, $B$)$,
  eff-typing($Gamma$, $epsilon$, $a$, $A$),
  eff-typing($Gamma$, $epsilon$, $f med a$, $B$),
)
#let expr-let1 = rule(
  label: msc("let1"),
  eff-typing($Gamma$, $epsilon$, $a$, $A$),
  eff-typing($Gamma, x : A$, $epsilon$, $b$, $B$),
  eff-typing($Gamma$, $epsilon$, letx($x$, $a$, $b$), $B$),
)
#let expr-unit = rule(
  label: msc("unit"),
  eff-typing($Gamma$, $epsilon$, $()$, $tyunit$),
)
#let expr-pair = rule(
  label: msc("pair"),
  eff-typing($Gamma$, $epsilon$, $a$, $A$),
  eff-typing($Gamma$, $epsilon$, $b$, $B$),
  eff-typing($Gamma$, $epsilon$, $(a, b)$, $A tytensor B$),
)
#let expr-let2 = rule(
  label: msc("let2"),
  eff-typing($Gamma$, $epsilon$, $e$, $A tytensor B$),
  eff-typing($Gamma, x : A, y : B$, $epsilon$, $c$, $C$),
  eff-typing($Gamma$, $epsilon$, letx($(x, y)$, $e$, $c$), $C$),
)
#let expr-inl = rule(
  label: msc("inl"),
  eff-typing($Gamma$, $epsilon$, $a$, $A$),
  eff-typing($Gamma$, $epsilon$, linl($a$), $A tysum B$),
)
#let expr-inr = rule(
  label: msc("inr"),
  eff-typing($Gamma$, $epsilon$, $b$, $B$),
  eff-typing($Gamma$, $epsilon$, linr($b$), $A tysum B$),
)
#let expr-abort = rule(
  label: msc("abort"),
  eff-typing($Gamma$, $epsilon$, $a$, $tyempty$),
  eff-typing($Gamma$, $epsilon$, labort($a$), $A$),
)
#let expr-case = rule(
  label: msc("case"),
  eff-typing($Gamma$, $epsilon$, $e$, $A tysum B$),
  eff-typing($Gamma, x : A$, $epsilon$, $a$, $C$),
  eff-typing($Gamma, y : B$, $epsilon$, $b$, $C$),
  eff-typing($Gamma$, $epsilon$, casex($e$, $x$, $a$, $y$, $b$), $C$),
)

#let region-br = rule(
  label: msc("br"),
  eff-typing($Gamma$, $effpure$, $a$, $A$),
  $sans("L")(ell) = A$,
  region-typing($Gamma$, ssa-branch($ell$, $a$), $sans("L")$),
)
#let region-let1 = rule(
  label: msc("let1-r"),
  eff-typing($Gamma$, $epsilon$, $a$, $A$),
  region-typing($Gamma, x : A$, $r$, $sans("L")$),
  region-typing($Gamma$, letx($x$, $a$, $r$), $sans("L")$),
)
#let region-let2 = rule(
  label: msc("let2-r"),
  eff-typing($Gamma$, $epsilon$, $e$, $A tytensor B$),
  region-typing($Gamma, x : A, y : B$, $r$, $sans("L")$),
  region-typing($Gamma$, letx($(x, y)$, $e$, $r$), $sans("L")$),
)
#let region-case = rule(
  label: msc("case-r"),
  eff-typing($Gamma$, $epsilon$, $e$, $A tysum B$),
  region-typing($Gamma, x : A$, $r$, $sans("L")$),
  region-typing($Gamma, y : B$, $s$, $sans("L")$),
  region-typing($Gamma$, casex($e$, $x$, $r$, $y$, $s$), $sans("L")$),
)
#let region-cfg = rule(
  label: msc("cfg"),
  region-typing($Gamma$, $r$, $sans("L"), (ell_i(A_i),)_(i in I)$),
  $forall i in I. #region-typing($Gamma, x_i : A_i$, $t_i$, $sans("L"), (ell_j(A_j),)_(j in I)$)$,
  region-typing(
    $Gamma$,
    ssa-where($r$, $(#ssa-clause($ell_i$, $x_i$, $t_i$),)_(i in I)$),
    $sans("L")$,
  ),
)

#let wk-nil = rule(label: msc("wk-nil"), $dot.op <= dot.op$)
#let wk-skip = rule(label: msc("wk-skip"), $Gamma <= Delta$, $Gamma, x : A <= Delta$)
#let wk-cons = rule(label: msc("wk-cons"), $Gamma <= Delta$, $Gamma, x : A <= Delta, x : A$)
#let lwk-nil = rule(label: msc("lwk-nil"), $dot.op <= dot.op$)
#let lwk-skip = rule(label: msc("lwk-skip"), $sans("L") <= sans("K")$, $sans("L") <= sans("K"), ell(A)$)
#let lwk-cons = rule(label: msc("lwk-cons"), $sans("L") <= sans("K")$, $sans("L"), ell(A) <= sans("K"), ell(A)$)

#let subst-typing(subst, source, target) = $#subst : #source mapsto #target$
#let sb-nil = rule(label: msc("sb-nil"), subst-typing($dot.op$, $Gamma$, $dot.op$))
#let sb-cons = rule(
  label: msc("sb-cons"),
  subst-typing($gamma$, $Gamma$, $Delta$),
  eff-typing($Gamma$, $effpure$, $e$, $A$),
  subst-typing($gamma, x mapsto e$, $Gamma$, $Delta, x : A$),
)

#let label-subst-typing(ctx, subst, source, target) = $#ctx ⊢ #subst : #source arrow.r.squiggly #target$
#let ls-nil = rule(
  label: msc("ls-nil"),
  label-subst-typing($Gamma$, $dot.op$, $dot.op$, $sans("K")$),
)
#let ls-cons = rule(
  label: msc("ls-cons"),
  label-subst-typing($Gamma$, $sigma$, $sans("L")$, $sans("K")$),
  region-typing($Gamma, x : A$, $r$, $sans("K")$),
  label-subst-typing($Gamma$, $sigma, ell(x) mapsto r$, $sans("L"), ell(A)$, $sans("K")$),
)
