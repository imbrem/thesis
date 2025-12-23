#import "../../syntax.typ": *

// Rules for Γ ⊢ a : A

#let r-var = rule(
  name: "var",
  $Γ med x = A$,
  $hasty(Γ, x, A)$,
);
#let r-coe = rule(
  name: "coe",
  $hasty(Γ, a, A)$,
  $tywk(A, A')$,
  $hasty(Γ, a, A')$,
);
#let r-app = rule(
  name: "app",
  $isfn(Γ, f, A, B)$,
  $hasty(Γ, a, A)$,
  $hasty(Γ, f med a, B)$,
);
#let r-inj = rule(
  name: "inj",
  $hasty(Γ, a, A)$,
  $hasty(Γ, lb("l") med a, Σ (lty(lb("l"), A)))$,
);
#let r-proj = rule(
  name: "proj",
  $hasty(Γ, e, Π (fty(lb("f"), A)))$,
  $hasty(Γ, lb("f") med e, A)$,
);
#let r-tuple = rule(
  name: "tuple",
  $istup(Γ, E, lb("T"))$,
  $hasty(Γ, (E), Π lb("T"))$,
);
#let r-pi-nil = rule(
  name: "Π-nil",
  $istup(Γ, ·, ·)$,
);
#let r-pi-cons = rule(
  name: "Π-cons",
  $istup(Γ, E, lb("T"))$,
  $hasty(Γ, e, A)$,
  $istup(Γ, #$E, e$, #$lb("T"), fty(lb("f"), A)$)$,
);
#let r-let = rule(
  name: "let",
  $hasty(Γ, a, A)$,
  $hasty(#$Γ, x : A$, b, B)$,
  $hasty(Γ, elet(x, a, b), B)$,
);
#let r-cases = rule(
  name: "cases",
  $hasty(Γ, e, Σ lb("L"))$,
  $isebrs(Γ, lb("L"), M, A)$,
  $hasty(Γ, ecase(e, M), A)$,
);
#let r-sigma-nil = rule(
  name: "Σ-nil",
  $isebrs(Γ, ·, ·, A)$,
);
#let r-sigma-cons = rule(
  name: "Σ-cons",
  $isebrs(Γ, lb("L"), M, A)$,
  $hasty(#$Γ, x : B$, a, A)$,
  $isebrs(Γ, #$lb("L"), lty(lb("l"), B)$, #$M, ebr(lb("l"), x, a)$, A)$,
);
#let r-iter = rule(
  name: "iter",
  $hasty(Γ, a, A)$,
  $hasty(Γ, e, B + A)$,
  $hasty(Γ, eiter(a, x, e), B)$,
);

#let r-csigma-nil = rule(
  name: "Σ-nil",
  $kebrs(·, ·, A)$,
)
#let r-csigma-cons = rule(
  name: "Σ-cons",
  $kebrs(cal(K), M, A)$,
  $hasty(#$Γ, x : B$, a, A)$,
  $kebrs(#$cal(K), clty(lb("l"), Γ, B)$, #$M, ebr(lb("l"), x, a)$, A)$,
)

// Congruence rules for Γ ⊢_Eq a ≈ b : A

#let req = ms("Eq")

#let r-eq-var = rule(
  name: "var",
  $Γ med x = A$,
  $tyeq(Γ, req, x, x, A)$,
)
#let r-eq-coe = rule(
  name: "coe",
  $tyeq(Γ, req, a, a', A)$,
  $tywk(A, A')$,
  $tyeq(Γ, req, a, a', A')$,
)
#let r-eq-app = rule(
  name: "app",
  $isfn(Γ, f, A, B)$,
  $tyeq(Γ, req, a, a', A)$,
  $tyeq(Γ, req, f med a, f med a', B)$,
)
#let r-eq-inj = rule(
  name: "inj",
  $tyeq(Γ, req, a, a', A)$,
  $tyeq(Γ, req, lb("l") med a, lb("l") med a', Σ (lty(lb("l"), A)))$,
)
#let r-eq-proj = rule(
  name: "proj",
  $tyeq(Γ, req, e, e', Π (fty(lb("f"), A)))$,
  $tyeq(Γ, req, lb("f") med e, lb("f") med e', A)$,
)
#let r-eq-tuple = rule(
  name: "tuple",
  $tupref(Γ, req, E, E', lb("T"))$,
  $tyeq(Γ, req, (E), (E'), Π lb("T"))$,
)
#let r-eq-pi-nil = rule(
  name: "Π-nil",
  $tupref(Γ, req, ·, ·, ·)$,
)
#let r-eq-pi-cons = rule(
  name: "Π-cons",
  $tupref(Γ, req, E, E', lb("T"))$,
  $tyeq(Γ, req, e, e', A)$,
  $tupref(Γ, req, #$E, e$, #$E', e'$, #$lb("T"), fty(lb("f"), A)$)$,
)
#let r-eq-let = rule(
  name: "let",
  $tyeq(Γ, req, a, a', A)$,
  $tyeq(#$Γ, x : A$, req, b, b', B)$,
  $tyeq(Γ, req, elet(x, a, b), elet(x, a', b'), B)$,
)
#let r-eq-cases = rule(
  name: "cases",
  $tyeq(Γ, req, e, e', Σ lb("L"))$,
  $ebrseq(Γ, lb("L"), req, M, M', A)$,
  $tyeq(Γ, req, ecase(e, M), ecase(e', M'), A)$,
)
#let r-eq-sigma-nil = rule(
  name: "Σ-nil",
  $ebrseq(Γ, ·, req, ·, ·, A)$,
)
#let r-eq-sigma-cons = rule(
  name: "Σ-cons",
  $ebrseq(Γ, lb("L"), req, M, M', A)$,
  $tyeq(#$Γ, x : A$, req, a, a', A)$,
  $ebrseq(
    Γ, #$lb("L"), lty(lb("l"), A)$, req,
    (#$M, ebr(lb("l"), x, a)$), (#$M', ebr(lb("l"), x, a')$),
    A
  )$,
)
#let r-eq-iter = rule(
  name: "iter",
  $tyeq(Γ, req, a, a', A)$,
  $tyeq(Γ, req, e, e', B + A)$,
  $tyeq(Γ, req, eiter(a, x, e), eiter(e', x, a'), B)$,
)

// Effect rules Γ ⊢_ε a : A

#let r-eff-var = rule(
  name: "var",
  $Γ med x = A$,
  $dehasty(Γ, ε, x, A)$,
)
#let r-eff-coe = rule(
  name: "coe",
  $dehasty(Γ, ε, a, A)$,
  $tywk(A, A')$,
  $dehasty(Γ, ε, a, A')$,
)
#let r-eff-app = rule(
  name: "app",
  $eisfn(Γ, ε, f, A, B)$,
  $dehasty(Γ, ε, a, A)$,
  $dehasty(Γ, ε, f med a, B)$,
)
#let r-eff-inj = rule(
  name: "inj",
  $dehasty(Γ, ε, a, A)$,
  $dehasty(Γ, ε, lb("l") med a, Σ (lty(lb("l"), A)))$,
)
#let r-eff-proj = rule(
  name: "proj",
  $ehasty(Γ, ε, e, Π (fty(lb("f"), A)))$,
  $dehasty(Γ, ε, lb("f") med e, A)$,
)
#let r-eff-tuple = rule(
  name: "tuple",
  $deistup(Γ, ε, E, lb("T"))$,
  $dehasty(Γ, ε, (E), Π lb("T"))$,
)
#let r-eff-pi-nil = rule(
  name: "Π-nil",
  $deistup(Γ, ε, ·, ·)$,
)
#let r-eff-pi-cons = rule(
  name: "Π-cons",
  $deistup(Γ, ε, E, lb("T"))$,
  $dehasty(Γ, ε, e, A)$,
  $deistup(Γ, ε, #$E, e$, #$lb("T"), fty(lb("f"), A)$)$,
)
#let r-eff-let = rule(
  name: "let",
  $dehasty(Γ, ε, a, A)$,
  $dehasty(#$Γ, x : A$, ε, b, B)$,
  $dehasty(Γ, ε, elet(x, a, b), B)$,
)
#let r-eff-cases = rule(
  name: "cases",
  $dehasty(Γ, ε, e, Σ lb("L"))$,
  $deisebrs(Γ, lb("L"), ε, M, A)$,
  $hasty(Γ, ecase(e, M), A)$,
)
#let r-eff-sigma-nil = rule(
  name: "Σ-nil",
  $deisebrs(Γ, ·, ε, ·, A)$,
)
#let r-eff-sigma-cons = rule(
  name: "Σ-cons",
  $deisebrs(Γ, lb("L"), ε, M, A)$,
  $dehasty(#$Γ, x : A$, ε, a, A)$,
  $deisebrs(Γ, #$lb("L"), lty(lb("l"), A)$, ε, #$M, ebr(lb("l"), x, a)$, A)$,
)
#let r-eff-iter = rule(
  name: "iter",
  $eisinf(ε)$,
  $dehasty(Γ, ε, a, A)$,
  $dehasty(Γ, ε, e, B + A)$,
  $dehasty(Γ, ε, eiter(a, x, e), B)$,
)

// Congruence rules for Γ ⊢_R a ->> b : A

#let rref = ms("R")

#let r-ref-var = rule(
  name: "var",
  $Γ med x = A$,
  $tyref(Γ, ms("R"), x, x, A)$,
)
#let r-ref-coe = rule(
  name: "coe",
  $tyref(Γ, ms("R"), a, a', A)$,
  $tywk(A, A')$,
  $tyref(Γ, ms("R"), a, a', A')$,
)
#let r-ref-app = rule(
  name: "app",
  $isfn(Γ, f, A, B)$,
  $tyref(Γ, ms("R"), a, a', A)$,
  $tyref(Γ, ms("R"), f med a, f med a', B)$,
)
#let r-ref-inj = rule(
  name: "inj",
  $tyref(Γ, ms("R"), a, a', A)$,
  $tyref(Γ, ms("R"), lb("l") med a, lb("l") med a', Σ (lty(lb("l"), A)))$,
)
#let r-ref-proj = rule(
  name: "proj",
  $tyref(Γ, ms("R"), e, e', Π (fty(lb("f"), A)))$,
  $tyref(Γ, ms("R"), lb("f") med e, lb("f") med e', A)$,
)
#let r-ref-tuple = rule(
  name: "tuple",
  $tupref(Γ, ms("R"), E, E', lb("T"))$,
  $tyref(Γ, ms("R"), (E), (E'), Π lb("T"))$,
)
#let r-ref-pi-nil = rule(
  name: "Π-nil",
  $tupref(Γ, ms("R"), ·, ·, ·)$,
)
#let r-ref-pi-cons = rule(
  name: "Π-cons",
  $tupref(Γ, ms("R"), E, E', lb("T"))$,
  $tyref(Γ, ms("R"), e, e', A)$,
  $tupref(Γ, ms("R"), #$E, e$, #$E', e'$, #$lb("T"), fty(lb("f"), A)$)$,
)
#let r-ref-let = rule(
  name: "let",
  $tyref(Γ, ms("R"), a, a', A)$,
  $tyref(#$Γ, x : A$, ms("R"), b, b', B)$,
  $tyref(Γ, ms("R"), elet(x, a, b), elet(x, a', b'), B)$,
)
#let r-ref-cases = rule(
  name: "cases",
  $tyref(Γ, ms("R"), e, e', Σ lb("L"))$,
  $ebrsref(Γ, lb("L"), ms("R"), M, M', A)$,
  $tyref(Γ, ms("R"), ecase(e, M), ecase(e', M'), A)$,
)
#let r-ref-sigma-nil = rule(
  name: "Σ-nil",
  $ebrsref(Γ, ·, ms("R"), ·, ·, ·)$,
)
#let r-ref-sigma-cons = rule(
  name: "Σ-cons",
  $ebrsref(Γ, lb("L"), ms("R"), M, M', A)$,
  $tyref(#$Γ, x : A$, ms("R"), a, a', A)$,
  $ebrsref(
    Γ, #$lb("L"), lty(lb("l"), A)$, ms("R"),
    (#$M, ebr(lb("l"), x, a)$), (#$M', ebr(lb("l"), x, a')$),
    A
  )$,
)
#let r-ref-iter = rule(
  name: "iter",
  $tyref(Γ, ms("R"), a, a', A)$,
  $tyref(Γ, ms("R"), e, e', B + A)$,
  $tyref(Γ, ms("R"), eiter(a, x, e), eiter(e', x, a'), B)$,
)