#import "@preview/drafting:0.2.2"

#let todos = counter("todos")

#let todo-inline(it) = [
  #[
    #set text(red.darken(20%))
    *TODO #context todos.display():* #it
    #todos.step()
  ] <no-wc>
]

#let todo(it) = block(todo-inline(it))

#let total-todos = context counter("todos").final().at(0)

#let max-words = 60000
#let percent-done = context {
  calc.round(decimal((100 * state("wordometer").final().words) / max-words), digits: 3)
}
#let p-doom = context {
  let prop-done = state("wordometer").final().words / max-words
  if prop-done > 0.9 {
    [*LOW*]
  } else if prop-done > 0.5 {
    [*MEDIUM*]
  } else {
    [*HIGH*]
  }
}

#let stats-box(production) = align(center, [
  // Alas for string keys! I feel dirty using this...
  #box(height: 7em, width: 30em, stroke: black)[
    #if not production {
      [
        *The current word count is* 
        $#(context state("wordometer").final().words) slash #max-words ≈ #percent-done%$ 
        complete.

        *There are $#total-todos$ TODOs remaining*

        $sans(P)(sans("doom"))$ is currently *#p-doom*
      ]
    }
  ] <no-wc>
])

#let margin-note(content, note) = drafting.margin-note(
  content,
  [ #note <no-wc> ]
)

#let scaffold(content) = [
  #set text(yellow.darken(50%))
  #content
]

#let block-notes(content) = [
  #set text(green.darken(50%))
  #content <no-wc>
]
