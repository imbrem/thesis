#import "/lib/prelude.typ": *

= Introduction

/* Take 1: */

The fundamental question of this thesis is:
_what does a computer program mean?_

We can approach this in two ways: from the bottom-up or the top-down.

The former tends to be more natural for computer scientists.

A computer is a machine for following instructions
--
a program is a sequence of instructions for it to follow.

In particular, a computer has an _instruction set_
--
a finite set of _operations_ which it can perform,
which read from and write to its _state_
--
that is, the current state of the registers, program counters,
memory, interrupts, and all the other bits which make a modern CPU tick.

Which is a _lot_.

/* Take 2: */

This thesis is about the _denotational semantics_ of the _static single assignment_ -- or _SSA_ -- compiler _intermediate representation_ -- or _IR_. 

I want to start by justifying this choice of topic.

- _Why_ do we need a semantics for a _compiler IR_?

  Because high-level languages have too many features to effectively study _or_ to lower in one pass.

  Because low-level languages are designed to be _executed_ efficiently -- making them difficult both to reason about or to lower in one pass.

- _Why_ should we use _SSA_ as our compiler IR?

  Practically: most modern compilers use it.

  Theoretically: it's right at the intersection of functional and imperative programming
  --
  letting us use it as a _thin waist_ to develop the _isomorphism_
  between the two.

- _Why_ should we give a _denotational_ semantics?

  Because we want to reason about programs _algebraically_
  --
  and to do so in a _compositional_ manner.