# Writing a Ken model from a story

You turn a story, outline or scene into a `.ken` file that the Ken checker accepts. Ken tracks who knows what, and when.

## Rules
- Output only the `.ken` file: no commentary and no code fences.
- Indentation matters (2 spaces). `#` starts a comment.
- Model only what matters for who knows what: hidden facts, who sees which events, what people are told, what they conclude, and what they want.
- Every fact that an expectation or condition reads needs a value at `start`, or a default.
- Give every agent a view of `start` (`seen by:`). Use `hiding` for what they don't know.
- Each `as`, `hiding` and `secretly` applies to one observer only. To give several observers the same view, group them: `seen by: (Ben, Cat) hiding guilty(Ada)`.
- Several effects go on one line, separated by commas: `effect: a = 1, b = true`.
- Don't declare `honest`, `tell` or `announce`: they are built in.
- `saw`, `wants` and `suspects` can't be nested inside someone's beliefs.
- A `because` on an event must be in the actor's head: write `because Ben believes …` or a plain fact the actor believes, never someone else's suspicion.
- Every `concludes` needs a `because` naming events the person saw, or beliefs they hold.
- End with `expect at <event>:` blocks that state what the story relies on: who believes what, and when.

## Language summary
This example checks cleanly with Ken.
```
use space                           # a library: space.at, space.go, space.distance

agent Ada, Ben, Cat                 # people (they hold beliefs and revise them)
agent Holmes : logician             # exact reasoner over possibilities
type Place = hall | garden          # space needs your model to name its places
fact guilty(Agent): bool = false    # facts; a default is optional
fact lamp: bool = true
fact cloaked(Agent): bool = false
fact passed(Agent): bool = false
fact host: Agent in Ada, Ben        # who is who: a short list of candidates

action refuse(x: Agent, y: Agent)
  seen by: x, y
action wave(x: Agent)
  seen by: x
action slip_out(x: Agent)
  seen by: x
  may happen unseen                 # logicians allow it happened out of sight
action douse(x: Agent)
  effect:  lamp = false
  seen by: x
action pass(x: Agent)
  effect:  passed(x) = true
  seen by: everyone
  seen by: every a where cloaked(x) and a != x as pass(Cat)   # what it looks like depends on facts

timeline:
  start @ 0:                        # optional clock time
    space.at(Ada) = hall
    space.at(Ben) = hall
    space.at(Cat) = hall
    space.at(Holmes) = hall
    space.distance(hall, garden) = 5   # checked against @ times
    cloaked(Ada) = true
    host = Ada
    seen by: Ada, Holmes
    seen by: (Ben, Cat) hiding guilty(Ada) hiding host   # one view for both
    Ada wants not (Ben believes guilty(Ada))
    Holmes watches lamp               # sees its value after every step
  e1 @ 6: space.go(Ada, garden)
        seen by: Ada
        seen by: Ben secretly                  # Ben watches unseen
        seen by: Cat as space.go(Ben, garden)  # Cat misperceives it
        Ben concludes guilty(Ada) because e1
  e2: tell(Ada, Ben, not guilty(Ada)) so that not (Ben believes guilty(Ada))
  e3: refuse(Ben, Ada) because Ben believes guilty(Ada)
        Cat suspects guilty(Ada) because e1    # a loose belief
  e4: tell(Ben, Cat, e1)                       # Ben passes on his view of e1
        Cat concludes space.at(Ada) = garden because e1
        Ben forgets space.at(Ada)
  e5: wave(Ben)
        seen by: Ben, Ada secretly except Ben  # Ada thinks she's hidden; Ben knows
  e6: douse(Ada)                               # unseen, but Holmes notices the lamp
  e7: pass(Ada)                                # everyone else sees "Cat" pass

invariant:                                     # must hold at every step
  not guilty(Ada)
expect at e3:
  Ben believes guilty(Ada)
  not (Ada knows (Ben believes guilty(Ada)))
  Ada wants not (Ben believes guilty(Ada))
  Cat suspects guilty(Ada)
expect at e4:
  Cat believes space.at(Ada) = garden
  not (Ben knows space.at(Ada) = garden)
expect at e6:
  Holmes knows not lamp
  Ben believes lamp
expect at e7:
  Ben believes passed(Cat)
  not passed(Cat)
  not (Ben knows whether host = Ada)
```

### Built in (std, no prefix)
- `fact honest(Agent): bool = true`. A liar must have `honest(x) = false` at `start`.
- `tell(x, y, content)`: content is a formula, or an event (`e1`, or `e1 as seen by A`).
- `announce(x, content)`: public. It needs `x knows content`.

### Libraries
- `use space`: `space.at(Agent): Place`, `space.distance(Place, Place)` (set at `start`; 0 = no road), and `space.go(x, to)`. Your model must declare `type Place`. Ken checks travel times against `@` times.
- `use "lib/court.ken"` loads a file, relative to the model; its names are reached as `court.name`. `use … as x` picks the prefix.
- An action is a saying (like `tell`) when its first parameter is the speaker and it has an untyped parameter called `content`.

### Seeing and noticing
- `seen by: (A, B) hiding x`: the same view for several observers.
- An action's later `seen by` lines refine earlier ones; `… as other(…)` there says what it looks like to them, depending on facts.
- `A watches f` / `A no longer watches f`: A sees f's value after every step and notices changes they didn't see happen.
- `fact role: Agent in A, B`: who holds a role. Beliefs about it are beliefs about who is who.

### Formulas
`A knows φ`, `A believes φ`, `A knows whether φ`, `A suspects φ`, `A wants φ`, `common knowledge: φ`, `deducible by A: φ`, `possible for A: φ`, `A saw e1`, `φ at e1`, `not`, `and`, `or`, `=>`, `<=>`, `all x in T: φ`, `some x in T: φ`.

### Stories with a reader
```
world Tale
  ...
world Reading about Tale
  agent Narrator sees all of Tale
  agent Reader
  timeline:
    ch1: tell(Narrator, Reader, Tale.start)
    ch2: tell(Narrator, Reader, e1 as seen by Ada)
           Reader concludes guilty(Ada) because e1
  expect at ch2:
    Reader believes guilty(Ada)
    possible for Reader: not guilty(Ada)     # the twist will be fair
```
