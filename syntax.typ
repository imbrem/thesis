// == Fonts ==

#let ms(txt) = $sans(txt)$
#let mb(txt) = $bold(txt)$
#let lb(txt, annot : none) = $mono(txt)_annot$

// == Branding ==

// Flat
#let while-flat = $ms("IMP")$
#let rtl-flat = $ms("RTL")$
#let ssa-flat = $ms("SSA")$
#let ssa-a-flat = $ms("SSA")_ms("A")$
#let rtl-a-flat = $ms("RTL")_ms("A")$

// λ
#let rtl-calc = $λ_ms("rtl")$
#let ssa-calc = $λ_ms("ssa")$
#let iter-calc=  $λ_ms("iter")$

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

// Standard names
#let ninl = $lb("i")_lb("l")$
#let ninr = $lb("i")_lb("r")$
#let nbr = $lb("b")$
#let ncn = $lb("c")$

// Types
#let tbool = $mb("2")$

// Punctuation
#let seq = $; thick$

// == Syntax ==

// Syntax for expressions
  
/// A branch of a case statement
#let ebr(ℓ, x, b) = $#ℓ (#x) : #b$

/// A let expression
#let elet(x, a, e) = $klet #x = #a seq #e$

/// A case expression
#let ecase(e, B) = $kcase #e thick { #B }$

/// An iteration expression
#let eiter(e, x, b) = $kiter #e thick { #ebr(ncn, x, b) }$

// Statements

#let brb(ℓ, ..vs) = if vs.pos().len() == 0 {
  $kbr #ℓ$
} else {
  $kbr #ℓ thick #vs.pos().at(0)$
}
#let retb(v) = $kret #v$
#let casestmt(e, B) = $kcase #e thick { #B }$
#let letstmt(x, a, t) = $klet #x = #a seq #t$

#let sbr(ℓ, x, b) = $#ℓ (#x) : #b$
//TODO: think about type annotations here...
#let lbb(ℓ, x, t) = $#ℓ (#x) : #t$

// Syntax sugar

/// A binary case expression
#let ecase2(e, x, a, y, b) = ecase(e, $ebr(ninl, #x, #a) seq ebr(ninr, #y, #b)$)

// Statements
#let ite(o, l, r) = $kif #o thick { #l } kelse { #r }$
#let switchstmt(e, B) = $kswitch #e thick { #B }$
#let linl(v) = $ninl med #v$
#let linr(v) = $ninr med #v$
#let casestmt2(e, x, s, y, t) = casestmt(e, $sbr(ninl, #x, #s) seq  sbr(ninr, #y, #t)$)

// Other languages
#let phistmt(branches) = $ϕ thick { #branches }$

// Judgements

#let bhyp(x, A, ..vs) = $#x : #A^(#vs.pos().at(0, default: none))$
#let lhyp(ℓ, A) = $#ℓ (#A)$
#let hasty(Γ, a, A) = $#Γ ⊢ #a : #A$
#let haslb(Γ, r, L) = $#Γ ⊢ #r triangle.stroked.small.r #L$
#let issubst(γ, Γ, Δ) = $#γ : #Γ => #Δ$
#let lbsubst(Γ, σ, L, K) = $#Γ ⊢ #σ : #L arrow.r.long.squiggly #K$
#let isop(f, A, B, ε) = $#f : #A ->^#ε #B$
#let tmeq(Γ, ε, a, b, A) = $#Γ ⊢_#ε #a equiv #b : #A$
#let lbeq(Γ, r, s, L) = $#Γ ⊢ #r equiv #s triangle.stroked.small.r #L$
#let tmseq(γ, γp, Γ, Δ) = $#γ equiv #γp : #Γ => #Δ$
#let lbseq(σ, σp, Γ, L, K) = $#Γ ⊢ #σ equiv #σp : #L arrow.r.long.squiggly #K$
#let cfgsubst(branches) = $⟨#branches⟩$
#let lupg(γ) = $upright(↑)#γ$
#let rupg(γ) = $#γ upright(↑)$