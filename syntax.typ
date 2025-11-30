#let ms(txt) = $sans(txt)$
#let mb(txt) = $bold(txt)$

#let klet = $ms("let")$
#let kmut = $ms("mut")$
#let kwhile = $ms("while")$
#let kif = $ms("if")$
#let kelse = $ms("else")$
#let kbr = $ms("br")$
#let kabort = $ms("abort")$
#let kbr = $ms("br")$
#let kret = $ms("ret")$
#let kcase = $ms("case")$
#let kswitch = $ms("switch")$
#let kwhere = $ms("where")$

#let ite(o, l, r) = $kif #o thick { #l } kelse { #r }$
#let linl(v) = $ι_l med #v$
#let linr(v) = $ι_r med #v$
#let labort(v) = $kabort #v$
#let seq = $; thick$
#let brb(ℓ, ..vs) = if vs.pos().len() == 0 {
  $kbr #ℓ$
} else {
  $kbr #ℓ thick #vs.pos().at(0)$
}
#let retb(v) = $kret #v$
#let caseexpr(e, B) = $kcase #e thick { #B }$
#let casestmt(e, B) = $kcase #e thick { #B }$
#let switchstmt(e, B) = $kswitch #e thick { #B }$
#let caseexpr2(e, x, a, y, b) = $kcase #e thick {linl(#x) : #a seq linr(#y) : #b}$
#let casestmt2(e, x, s, y, t) = $kcase #e thick {linl(#x) : #s seq linr(#y) : #t}$
#let wbranch(ℓ, x, t) = $#ℓ (#x) : #t$
#let where(t, L) = $#t thick kwhere {#L}$
#let letstmt(x, a, t) = $klet #x = #a seq #t$
#let letexpr(x, a, e) = $klet #x = #a seq #e$
#let bhyp(x, A, ..vs) = $#x : #A^(#vs.pos().at(0, default: none))$
#let lhyp(ℓ, A) = $#ℓ (#A)$
#let hasty(Γ, ε, a, A) = $#Γ ⊢_#ε #a : #A$
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