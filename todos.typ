#let todos = counter("todos")

#let todo-inline(it) = [
  #set text(red)
  *TODO #context todos.display():* #it
  #todos.step()
]

#let todo(it) = block(todo-inline(it))
