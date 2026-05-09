// Theorem, lemma, proof environments (ctheorems wrapper).

#import "@preview/ctheorems:1.1.3": thmbox, thmplain, thmproof, thmrules

#let theorem = thmbox("theorem", "Theorem", fill: rgb("#eeffee"), breakable: true, width: 100%)
#let lemma = thmbox("lemma", "Lemma", fill: rgb("#eef4ff"), breakable: true, width: 100%)
#let corollary = thmplain("corollary", "Corollary", base: "theorem", titlefmt: strong)
#let definition = thmbox("definition", "Definition", fill: rgb("#fff8ee"), breakable: true, width: 100%)
#let example = thmplain("example", "Example", titlefmt: strong)
#let remark = thmplain("remark", "Remark", titlefmt: strong)
#let proof = thmproof("proof", "Proof")
