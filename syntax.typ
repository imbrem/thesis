#import "@preview/lemmify:0.1.8": *
#import "@preview/curryst:0.6.0": prooftree, rule, rule-set
#import "@preview/fletcher:0.5.8" as fletcher: diagram, edge, node
#import "@preview/typsy:0.2.1": safe-state
#import "@preview/simplebnf:0.1.1": *

#let (
  theorem,
  lemma,
  corollary,
  remark,
  proposition,
  example,
  proof,
  rules: thm-rules,
) = default-theorems("thm-group", thm-numbering: thm-numbering-linear, lang: "en")

#let (
  definition,
  rules: thm-rules-b,
) = default-theorems("thm-group-b", thm-numbering: thm-numbering-linear, lang: "en")

// == Fonts ==

#let ms(txt) = $sans(txt)$
#let mb(txt) = $bold(txt)$
#let lb(txt) = $mono(txt)$

// == Branding ==

// Flat
#let while-flat(..xs) = if xs.pos().at(0, default: none) == none {
  $ms("IMP")$
} else {
  $ms("IMP")[#xs.pos().at(0)]$
}
#let rtl-flat(..xs) = if xs.pos().at(0, default: none) == none {
  $ms("RTL")$
} else {
  $ms("RTL")[#xs.pos().at(0)]$
}
#let ssa-a-flat(..xs) = if xs.pos().at(0, default: none) == none {
  $ms("SSA")$
} else {
  $ms("SSA")[#xs.pos().at(0)]$
}
#let rtl-a-flat(..xs) = if xs.pos().at(0, default: none) == none {
  $ms("RTL")_ms("A")$
} else {
  $ms("RTL")_ms("A")[#xs.pos().at(0)]$
}

// λ
#let rtl-calc(..xs) = if xs.pos().at(0, default: none) == none {
  $λ_ms("rtl")$
} else if xs.pos().at(1, default: none) == none {
  $λ_ms("rtl")[#xs.pos().at(0)]$
} else {
  $λ_ms("rtl")[#xs.pos().at(0), #xs.pos().at(1)]$
}

#let grtl-calc(..xs) = if xs.pos().at(0, default: none) == none {
  $λ_ms("rtl")^*$
} else {
  $λ_ms("rtl")^*[#xs.pos().at(0)]$
}

#let br-calc(..xs) = if xs.pos().at(0, default: none) == none {
  $λ_ms("br")$
} else if xs.pos().at(1, default: none) == none {
  $λ_ms("br")[#xs.pos().at(0)]$
}

#let ssa-calc(..xs) = if xs.pos().at(0, default: none) == none {
  $λ_ms("ssa")$
} else if xs.pos().at(1, default: none) == none {
  $λ_ms("ssa")[#xs.pos().at(0)]$
} else {
  $λ_ms("ssa")[#xs.pos().at(0), #xs.pos().at(1)]$
}

#let gssa-calc(..xs) = if xs.pos().at(0, default: none) == none {
  $λ_ms("ssa")^*$
} else if xs.pos().at(1, default: none) == none {
  $λ_ms("ssa")^*[#xs.pos().at(0)]$
} else {
  $λ_ms("ssa")^*[#xs.pos().at(0), #xs.pos().at(1)]$
}

#let op-calc(..xs) = if xs.pos().at(0, default: none) == none {
  $λ_ms("op")$
} else {
  $λ_ms("op")[#xs.pos().at(0)]$
}

#let iter-calc(..xs) = if xs.pos().at(0, default: none) == none {
  $λ_ms("iter")$
} else {
  $λ_ms("iter")[#xs.pos().at(0)]$
}

#let seq-calc(..xs) = if xs.pos().at(0, default: none) == none {
  $λ_ms("seq")$
} else {
  $λ_ms("seq")[#xs.pos().at(0)]$
}

#let case-calc(..xs) = if xs.pos().at(0, default: none) == none {
  $λ_ms("case")$
} else {
  $λ_ms("case")[#xs.pos().at(0)]$
}


#let dssa-calc(..xs) = if xs.pos().at(0, default: none) == none {
  $λ_ms("dssa")$
} else if xs.pos().at(1, default: none) == none {
  $λ_ms("dssa")[#xs.pos().at(0)]$
} else {
  $λ_ms("dssa")[#xs.pos().at(0), #xs.pos().at(1)]$
}

#let dgssa-calc(..xs) = if xs.pos().at(0, default: none) == none {
  $λ_ms("dssa")^*$
} else if xs.pos().at(1, default: none) == none {
  $λ_ms("dssa")^*[#xs.pos().at(0)]$
} else {
  $λ_ms("dssa")^*[#xs.pos().at(0), #xs.pos().at(1)]$
}

#let expr2fun(E) = $ms("LN")(#E)$

// Types
#let sty(..xs) = if xs.pos().at(0, default: none) == none {
  $ms("Ty")$
} else {
  $ms("Ty")[#xs.pos().at(0)]$
}

// Order theory
#let uua = math.class("unary", $↑$)
#let ula = math.class("unary", $↓$)
#let ubs(A) = $uua #A$
#let lbs(A) = $ula #A$

// == Tokens ==

// Keywords

// Basic
#let klet = $ms("let")$
#let kbr = $ms("br")$
#let kcase = $ms("case")$
#let kiter = $ms("iter")$

// Sugar
#let kif = $ms("if")$
#let kelse = $ms("else")$
#let kwhile = $ms("while")$
#let kmut = $ms("mut")$
#let kabort = $ms("abort")$
#let kret = $ms("ret")$
#let kswitch = $ms("switch")$

// Types
#let tzero = $mb("0")$
#let tunit = $mb("1")$
#let tbool = $mb("2")$
#let tlist(A) = $mb("List") med #A$

// Injections and projections
#let kwl = $ms("l")$
#let kwr = $ms("r")$

#let linj = $ι_kwl$
#let rinj = $ι_kwr$

#let nbr = kwl
#let ncn = kwr

#let lpi = $π_kwl$
#let rpi = $π_kwr$

// Orders
#let sle(..xs) = if xs.pos().len() == 1 {
  $scripts(⊑)_(#xs.pos().at(0))$
} else {
  $scripts(⊑)$
}

// Finite sets
#let kfin = $ms("Fin")$
#let fin(n) = $kfin #n$
#let kfcanon = $α_ms("Fin")^+$
#let fcanon(n, m) = $kfcanon(n, m)$

// Collections
#let cix(a) = $ms("ix")(#a)$
#let sdiff = $backslash$
#let csel(a, i) = $#a [#i]$
#let crem(a, i) = $#a sdiff #i$
#let cmap = $op("⟨$⟩")$
#let capp = $op("⟨⋆⟩")$
#let czip = $op("⟨,⟩")$
#let crix = $op("⟨#⟩")$
#let cfam = $ms("Fam")$
#let cthin = $ms("Thin")$
#let cperm = $ms("Perm")$
#let hfam(A, B) = $cfam(#A, #B)$
#let hthin(A, B) = $cthin(#A, #B)$
#let hperm(A, B) = $cperm(#A, #B)$

#let lthin(a, b) = $lpi (#a, #b)$
#let rthin(a, b) = $rpi (#a, #b)$

#let fnum(n) = $lb("p")_#n$
#let inum(n) = $lb("i")_#n$

#let tybase(A) = $ms("coe") med #A$

#let lab = $ms("lab")$
#let fld = $ms("fld")$

#let labhi(L, l) = $ms("hi")(#L, #l)$
#let lablo(L, l) = $ms("lo")(#L, #l)$
#let fldhi(F, f) = $ms("hi")(#F, #f)$
#let fldlo(F, f) = $ms("lo")(#F, #f)$

#let fty(f, A) = $#f : #A$
#let lty(l, A) = $#l (#A)$
#let fexpr(f, e) = $#f : #e$

#let clty(l, Γ, A) = $#l [#Γ] (#A)$

// Lists
#let lnil = $[ med ]$
#let llen(A) = $|#A|$
// A single math "+" glyph as content
#let mplus = $+$

// Compact “++” built by overlaying two pluses
#let lcat = math.op(
  box(width: 1.0em, height: 0.7em)[
    #place(center, dx: -0.15em, mplus)
    #place(center, dx: 0.15em, mplus)
  ],
)

#let lsnoc = $op(":+")$

#let compat(C) = $;_#C$
#let famcomp = compat(ms("Fam"))

// Sets
#let site(c, t, f) = $ms("if") #c ms("then") #t ms("else") #f$
#let icol(a) = $bold(upright(#a))$
#let sfam(A) = $bold(upright(#A))$
#let pset(X) = $cal(P)(X)$

#let sffam(A) = $A^ms("fin")$

#let famle = $⊑$

#let fmark = $ms("fin")$
#let fset(X) = $cal(P)_fmark(X)$
#let fdiff = $op(scripts(=)_fmark)$

#let ucof = $∀^c$
#let ecof = $∃^c$

#let pfn = $harpoon$
#let rfn = $arrow.r.struck$

#let brel(R, a, b) = $#a class("binary", #R) #b$

#let stor(R) = $⟨#R⟩$

#let scol = $class("normal", ⊕)$
#let tcol = $class("normal", ⊗)$

#let lflat(a) = $μ #a$
#let listof(A) = $#A^*$

#let grof(f) = $ms("gr")(#f)$

#let wbaglift(R, S) = $#R^ms("bag")_#S$
#let baglift(R) = $#R^ms("bag")$

#let dropm = $class("normal", !)$

#let foldn(R, n) = $ms("fold")_#n med #R$
#let fold(R) = $ms("fold") med #R$
#let cofoldn(R, n) = $ms("cofold")_#n med #R$
#let cofold(R) = $ms("cofold") med #R$
#let lfoldn(R, n) = $#R^([#n])$
#let lfold(R) = $#R^([*])$

// Categories
#let cset = $ms("Set")$
#let cposet = $ms("Poset")$
#let cpreord = $ms("PreOrd")$
#let cconc = $ms("Conc")$

#let piinj(A, B, i) = $ms("inj")(#A, #B, #i)$
#let ahm(C) = $scripts(->)_#C$
#let opc(C) = $#C^ms("op")$
#let opm(f) = $#f^ms("op")$
#let scat(C) = $sfam(cal(#C))$
#let munit = $upright(I)$

#let clet(f) = $ms("let")(#f)$
#let ccase(f) = $ms("case")(#f)$

#let distl(A, L) = $δ_(#A, #L)$
#let idistl(A, L) = $δ^(-1)_(#A, #L)$

#let ntag(n, A) = $n · A$

// Punctuation
#let seq = $; thick$
#let ovrd = $triangle.stroked.small.l$

// == Syntax ==

// Syntax for expressions

/// A branch in a case expression
#let ebr(ℓ, x, b) = $#ℓ (#x) : #b$

/// A let expression
#let elet(x, a, e) = $klet #x = #a seq #e$

/// A case expression
#let ecase(e, B) = $kcase #e thick { #B }$

/// An iteration expression
#let eiter(e, x, b) = $kiter #e thick { #ebr(ncn, x, b) }$

// Statements

/// An unconditional branch
#let brb(ℓ, ..vs) = if vs.pos().len() == 0 {
  $kbr #ℓ$
} else {
  $kbr #ℓ thick #vs.pos().at(0)$
}

/// A let statement
#let slet(x, a, t) = $#x = #a seq #t$

/// A case statement
#let scase(e, B) = $kcase #e thick { #B }$

/// A branch in a case statement
#let sbr(ℓ, x, b) = $#ℓ (#x) : #b$

#let gbr(ℓ, x, b) = $#ℓ (#x) : #b$

/// A labelled basic block
#let lbb(ℓ, x, t) = $#ℓ (#x) : #t$

// Syntax sugar

/// A return statement
#let retb(v) = $kret #v$

/// An if-then-else
#let ite(o, l, r) = $kif #o thick { #l } kelse { #r }$

/// A switch statement
#let sswitch(e, B) = $kswitch #e thick { #B }$

/// A branch in a switch statement
#let ssbr(ℓ, b) = $#ℓ : #b$

/// A binary case expression
#let ecase2(e, x, a, y, b) = ecase(e, $ebr(ninl, #x, #a) seq ebr(ninr, #y, #b)$)

/// A binary case statement
#let scase2(e, x, s, y, t) = scase(e, $sbr(ninl, #x, #s) seq sbr(ninr, #y, #t)$)

/// A φ-expression
#let eϕ(branches) = $ϕ thick { #branches }$

// Judgements

#let bhyp(x, A, ..vs) = $#x : #A^(#vs.pos().at(0, default: none))$
#let lhyp(ℓ, A) = $#ℓ (#A)$

#let tyle(..xs) = sle(sty(..xs))

#let atywk(A, B, ..xs) = $#A tyle(..xs) #B$

#let ktywk = sle()
#let klbwk = sle()

#let tywk(A, B) = $#A ktywk #B$
#let lbwk(L, M) = $#L klbwk #M$

#let kcwk = sle()
#let klbwk = sle()
#let kclbwk = sle()

#let cwk(Γ, Δ) = $#Γ kcwk #Δ$
#let lbcwk(L, M) = $#L klbwk #M$
#let clbwk(K, M) = $#K kclbwk #M$

#let kqwk = sle()

#let qwk(ql, qr) = $#ql kqwk #qr$

#let isfn(Γ, f, A, B) = $#Γ ⊢ #f : #A → #B$
#let istup(Γ, E, T) = $#Γ ⊢ #E scripts(:)^* #T$

#let hasty(Γ, a, A) = $#Γ ⊢ #a : #A$
#let haslb(Γ, r, L) = $#Γ ⊢ #r triangle.stroked.small.r #L$

#let kebrs(K, B, A) = $#K ⊢ #B scripts(:) #A$
#let ksbrs(K, B, L) = $#K ⊢ #B triangle.stroked.small.r #L$
#let klbrs(K, B, L) = $#K ⊢ #B triangle.stroked.small.r #L$

#let csplat = $*$

#let isebrs(Γ, L, B, A) = kebrs($#Γ csplat #L$, B, A)
#let issbrs(Γ, K, B, L) = ksbrs($#Γ csplat #K$, B, L)
#let islbrs(Γ, K, B, L) = klbrs($#Γ csplat #K$, B, L)

#let eisfn(Γ, e, f, A, B) = $#Γ scripts(⊢)^#e #f : #A → #B$
#let dehasty(Γ, e, a, A) = $#Γ scripts(⊢)^(≡#e) #a : #A$
#let deistup(Γ, e, E, T) = $#Γ scripts(⊢)^(≡#e) #E scripts(:)^* #T$
#let deisebrs(Γ, L, e, B, A) = $#Γ csplat #L scripts(⊢)^(≡#e) #B scripts(:)^* #A$
#let eisinf(e) = $∞(#e) = #e$

#let ehasty(Γ, e, a, A) = $#Γ scripts(⊢)^#e #a : #A$
#let eistup(Γ, e, E, T) = $#Γ scripts(⊢)^#e #E scripts(:)^* #T$
#let eisebrs(Γ, L, e, B, A) = $#Γ csplat #L scripts(⊢)^#e #B scripts(:)^* #A$
#let ehaslb(Γ, e, r, L) = $#Γ scripts(⊢)^#e #r triangle.stroked.small.r #L$

#let tyeq(Γ, Eq, a, b, A) = $#Γ scripts(⊢)_#Eq #a ≈ #b : #A$
#let tupeq(Γ, Eq, E, F, T) = $#Γ scripts(⊢)_#Eq #E ≈ #F scripts(:)^* #T$
#let ebrseq(Γ, L, Eq, B, B2, A) = $#Γ csplat #L scripts(⊢)_#Eq #B ≈ #B2 scripts(:)^* #A$
#let lbeq(Γ, Eq, s, t, L) = $#Γ scripts(⊢)_#Eq #s ≈ #t triangle.stroked.small.r #L$


#let tyquant(U, A, q) = $#U ⊢ #A^#q$
#let lquant(U, L, q) = $#U ⊢ #L^#q$
#let cquant(U, Γ, q) = $#U ⊢ #Γ^#q$

#let qlin = $1$
#let qrel = $+$
#let qaff = $?$
#let qint = $*$

#let tqlin = $1$
#let tqrel = $(+)$
#let tqaff = $(op(?))$
#let tqint = $(*)$

#let isaff(U, A) = $tyquant(#U, #A, qaff)$
#let isrel(U, A) = $tyquant(#U, #A, qrel)$

#let utywk(U, A, B) = $#A scripts(≤)_#U #B$
#let ulbwk(U, L, M) = $#L scripts(≤)_#U #M$

#let uctxwk(U, Γ, Δ) = $#Γ scripts(≤)_#U #Δ$
#let ulbcwk(U, L, M) = $#L scripts(≤)_#U #M$
#let uclbwk(U, K, M) = $#K scripts(≤)_#U #M$

#let tysplits(U, A, B, C) = $#A scripts(=>)_#U #B ⊗ #C$
#let usplits(U, Γ, Δ, Ξ) = $#Γ scripts(=>)_#U #Δ ⊗ #Ξ$

#let uisfn(Γ, U, f, A, B) = $#Γ scripts(⊢)_#U #f : #A → #B$
#let uhasty(Γ, U, a, A) = $#Γ scripts(⊢)_#U #a : #A$
#let uhaslb(Γ, U, r, L) = $#Γ scripts(⊢)_#U #r triangle.stroked.small.r #L$
#let uistup(Γ, U, E, T) = $#Γ scripts(⊢)_#U #E scripts(:)^* #T$
#let uisebrs(Γ, U, L, B, A) = $#Γ csplat #L scripts(⊢)_#U #B scripts(:)^* #A$

#let tyref(Γ, R, a, b, A) = $#Γ scripts(⊢)_#R #a ->> #b : #A$
#let tupref(Γ, R, E, F, T) = $#Γ scripts(⊢)_#R #E ->> #F scripts(:)^* #T$
#let ebrsref(Γ, L, R, B, B2, A) = $#Γ csplat #L scripts(⊢)_#R #B ->> #B2 scripts(:)^* #A$
#let lbref(Γ, R, s, t, L) = $#Γ scripts(⊢)_#R #s ->> #t triangle.stroked.small.r #L$

#let lupg(γ) = $upright(↑)#γ$
#let rupg(γ) = $#γ upright(↑)$

#let print-rule(..xs) = {
  prooftree.with(vertical-spacing: 0.2em)(..xs)
};

#let declare-rule(p, ..xs) = [
  #let named = xs.named();
  #let l = named.remove("label", default: none);
  #figure(
    print-rule(p, ..xs.pos(), ..named),
    kind: "rule",
    supplement: [(#p.name)],
  ) #l
]

#let deriv(j) = $ms("deriv")(#j)$

#let boxed(A) = box(A, stroke: black, inset: 0.75em)

#let rule-unnamed(r) = {
  r.name = none
  prooftree(r)
}

#let dntree(r) = $⟦#rule-unnamed(r)⟧$

#let denote-rule(r, d) = (
  rule: r,
  den: d,
)

#let dntty(j, t) = align(center, block(stroke: black, inset: 0.75em, $⟦#j⟧ : #t$))

#let dntdef(r, d) = $#dntree(r) &:= #d$

#let eqn-set(column-gutter: 3em, row-gutter: 2em, ..eqns) = align(center, block(
  // stroke: black,
  inset: (y: 0.5em),
  {
    set par(leading: row-gutter)
    block(eqns.pos().map(box).join(h(column-gutter, weak: true)))
  },
))

#let eqn-astack(..eqns) = align(center, block(
  // stroke: black,
  {
    eqns.pos().fold($$, (acc, eqn) => $acc \ \ eqn$)
  },
))

#let req = ms("Eq")
#let rref = ms("R")

#let show-syntax(body) = [
  #show: thm-rules
  #show: thm-rules-b

  #body
]

#let the-bibliography = bibliography("refs.bib", style: "acm-edited.csl")

#let standalone-state = (
  is-standalone: true,
  is-appendix: false,
)

#let body-state = (
  is-standalone: false,
  is-appendix: false,
)

#let appendix-state = (
  is-standalone: false,
  is-appendix: true,
)

#let thesis-state = safe-state(() => {}, standalone-state)

#let cdem = gray.darken(50%)
#let dem(x) = text(cdem, x)
