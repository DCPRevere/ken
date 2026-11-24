# Ken — specification v1.0

Ken describes **worlds** in which **agents** observe **events**, form **beliefs**, and act on them. A checker verifies that what you wrote is consistent and that your `expect` claims hold.

Stories, puzzles, games and protocols are all just worlds. See `ken-changelog.md` for how the design got here.

---

## 1. Principles

1. **Truth and belief are separate.** Events change what is true. Agents learn only from events.
2. **Everyone knows how the world works.** Types, actions, rules and their default `seen by` clauses are common knowledge. Values and particular events are not.
3. **Seeing includes seeing others see.** Whoever sees an event knows who else saw it and what shape of view they got, unless an observer is `secretly` present.
4. **Not seeing is seeing.** Because everyone knows who would see what, missing an event you would have seen is itself information.
5. **A view can differ from reality.** It can be complete, partial, mistaken, or have parts hidden.
6. **Everything happens in time.** Every fact and every belief holds at a point in time.
7. **There is only one kind of agent.** Characters, readers and narrators are all agents. A reader is an agent in a world whose events are tellings of another world.
8. **Memory follows the person, not the clock.** A person's beliefs run along their own experience. With time travel, that can carry knowledge "backwards" in world time.

---

## 2. Declarations

```
agent Sally, Anne                        # mode: person (default)
agent Islander[1..n] : logician          # an indexed group
type Colour = blue | brown
type Day = 14 .. 19
type Date = (month: Month, day: Day)     # a record
fact good(Agent): bool                   # can change over time
fact gone(Islander): bool = false        # with a starting value
fact captain: Agent in Ada, Ben          # only these values are possible
given n, blue                            # parameters supplied when checking
```

| Mode | How it reasons | Use for |
|---|---|---|
| `person` | One committed belief per fact, each with a recorded source. Models other minds the same way, to any depth. | Story characters, readers |
| `logician` | Keeps every possible world consistent with what it has seen. Believes φ when φ holds in all of them. | Puzzles, detectives |

**Who is who.** Roles are agent-valued facts, so mistaken identity is a belief about one: `fact captain: Agent in Capitaine, Dubois`, then `Aubrey believes surgeon = Capitaine` or `Aubrey believes not alive(captain)`. Inside a belief, `captain` means whoever the believer takes the captain to be. Keep the `in` list short: each hidden agent-valued fact multiplies the possibilities.

---

## 3. Actions and views

```
action put(who: Agent, to: Place)
  needs:   present(who)                  # precondition: an error if it's false
  effect:  marble = to
  seen by: every a where present(a)      # the default observers
```

- `seen by` is evaluated in the state just **before** the action.
- If `seen by` is omitted, nobody sees the action.
- An event in the timeline may give its own `seen by` lines. These **replace** the default for that event.

**Views**, written in `seen by` clauses:

| Clause | The observer gets |
|---|---|
| `seen by: B, C` | The full event. |
| `seen by: A as kill(B, C)` | A different description: partial or mistaken. |
| `seen by: X hiding content` | The fact that it happened, but not the hidden part. |
| `seen by: A secretly` | A full view, and other observers don't know A saw. Can be combined with `as` or `hiding`. |
| `seen by: A secretly except B and C` | As `secretly`, but B and C know A saw, and know A thinks nobody knows. A doesn't know they know. |
| `seen by: (A, B, C) hiding x` | One view shared by several observers: each gets `hiding x`. |

- Each modifier (`as`, `hiding`, `secretly`) applies to the one observer just before it, or to every name in a bracketed group. Ken warns when `seen by: A, B as …` looks as if it meant both.
- **Appearances**: an action may have several `seen by` lines. Later lines refine earlier ones for the observers they cover, and a line with `as` says what the action looks like to them, depending on the facts:
  ```
  action come_in_sight(x: Agent, s: Ship)
    effect:  sighted = s
    seen by: everyone
    seen by: every a where rigged_as_whaler and a != x as come_in_sight(x, whaler)
  ```
  The condition is evaluated in each possible world, so someone unsure whether the ship is disguised is unsure what others saw. The observers in the condition take the appearance at face value: if one of them knows better, leave them out of it.
- `effect:` may continue on indented lines, one or more assignments per line.
- **`may happen unseen`** on an action: a logician who doesn't see a step allows that any instance of the action happened then, out of their sight, unless they would have seen it. Persons don't; they revise when surprised instead (section 6).

---

## 4. Rules

```
rule leaving:
  after night(k), for every Islander i:
    when i knows eyes(i) and not gone(i):
      do leave(i)

private rule suspicion:                  # private: not common knowledge
  after A sees sneak_out(x):
    when A believes not good(x):
      A concludes plotting(x)
```

- `after e` fires when an event happens. `after A sees e` fires when A sees it.
- Actions a rule triggers become **part of the triggering event**. They can trigger further rules, up to 8 rounds.

---

## 5. Timeline

```
timeline:
  start:                                 # the first event: sets the initial state
    marble = basket
    seen by: Sally, Anne

  e1: attack(C, D) then kill(B, C)       # a compound event
        seen by: B, C, D
        seen by: A as kill(B, C)
        A concludes not good(B) because e1

  e2: refuse_help(A, B) because A believes plotting(B)

  night(k) for k in 1 .. n               # repeated events
```

- `start` fixes every fact: declared starting values plus its own assignments. Its views cover the whole initial state.
- **Clock times**: `e1 @ 10:` gives an event a time, in whatever unit you like. Times must not run backwards.
- **Travel** (with `use space`): `space.at(x)` says where someone is and `space.distance(a, b) = n`, set at `start`, is a road (either way; 0 means none). Someone's place is pinned at `start` and at each timed event they take part in; between two pins the time must cover the shortest route.
- **Motives**: `A wants φ` (from this event on) and `A no longer wants φ`. On an event, `so that φ` says what the actor (the first agent argument of its first action) means to bring about.
- **Suspicion**: `A suspects φ because e…` records a loose belief. It doesn't change what A believes.
- **Forgetting**: `A forgets <fact>` makes A unsure of its value again. `A forgets <event>` drops A's memory of the event.
- **Watching**: `A watches <fact>` (from this event on) and `A no longer watches <fact>`. After every step, A sees the fact's current value, even if A didn't see what changed it. A person who expected another value notices and assumes it changed out of sight. Others don't learn what A saw.
- **Time points**: `start`, `end`, an event name `e` (meaning just after e), and `before e`.
- **Reasons for acting**: a `because` on an event is checked just before it, and it must be in the actor's head (the actor is the first agent argument of the first action). A part about the actor's own mind (`A believes …`, `A wants …`, `A suspects …`, `A saw …`) is checked as written. Any other part φ is checked as `A believes φ`. A part about someone else's wants, suspicions or sightings is an error, because Ken can't nest those inside a belief. The reason itself is the author's to give: Ken checks that the actor could hold it, not that it is a good reason.
- A `because` on a conclusion records the source of the belief. The person must have seen or heard each cited event, by then, and must hold each cited belief. Ken doesn't judge whether the sources are good evidence; that is the character's psychology, and the author's call. A conclusion with no `because` gets a warning.

---

## 6. Belief

### Persons

A person's beliefs have three sources:

1. **Events they believe happened**, either seen or reported by someone they trust. They believe the view, its effects and its preconditions. If the event was a `tell` from someone they trust, they also believe its content. Anything not affected keeps its old value.
2. **Rules** that conclude something.
3. **The author**: `A concludes φ because <sources>`.

- **Trust**: a person trusts x unless they believe `not honest(x)`.
- **Other minds**: for each event a person believes happened, they update their model of every agent they believe saw it, using that agent's view. Everyone else's model stays unchanged. This applies recursively.
- **Retraction**: a concluded belief is retracted when one of its sources changes, either because the agent's view of a source event changes or because a source belief is retracted. Retraction cascades. A conclusion written `… despite <source>` survives changes to that source. This is stubbornness.
- **New views**: a new view of an event replaces the old one if it contains it, meaning the agent saw more of the same event. Otherwise it is a **conflict** the author must resolve with a conclusion of that agent that rests on the event (`because e1`). The new view then replaces the old.
- **Revision**: persons revise rather than break.
  - Seeing an event, or trusting testimony, that contradicts their beliefs about a *changeable* fact: they assume it changed unseen.
  - Testimony that contradicts their beliefs about an *unchangeable* fact, or that adds nothing, is ignored.
  - Concluding `not honest(x)` withdraws, retroactively, everything x told them and every conclusion resting on x's tellings.
  - A conclusion that contradicts earlier testimony sets the newest such testimony aside, and drops only those of their own conclusions that no longer fit.
  - A conclusion about a changeable fact that their observations rule out is taken as "it has changed".
  - `A concludes (B believes φ)`: A comes to think B privately believes φ.

- **Revision by recency** (when a person's beliefs clash with something new): their own conclusions and the testimony they accepted are all dropped, then each is kept back, newest first, while everything still fits. At the same step, their own conclusion beats testimony. Ken reports what had to go.
- **Announcements** are testimony for persons, like `tell`.
- **Suspicion** `A suspects φ` holds while the suspicion stands and A doesn't believe `not φ`. It lapses when a source event's view changes, or when A comes to believe the opposite.
- **Forgetting a fact** is a private update: in A's possible worlds the fact takes every value.

### Logicians

A logician keeps a set of possible worlds.

- When it sees an event, each world produces its own version of the event under the rules. It drops every world whose version it would have seen differently.
- A logician believes the content of a `tell` only when the action's preconditions guarantee it (see `announce`).
- A logician assumes nothing happened that they didn't see, except actions marked `may happen unseen`.

### Both

- **Knows** = believes, and it is true.

---

## 7. Formulas

```
A knows φ           A believes φ           A knows whether φ
A knows <term>      # knows its value: "Albert knows birthday"
common knowledge among G: φ                # or "common knowledge: φ" for everyone
deducible by A: φ   # a logician who saw and trusted what A did would know φ
possible for A: φ   # what A saw and trusted doesn't rule φ out
not  and  or  =>  <=>      all x in T: φ      some x in T: φ
φ at e              # φ held just after event e
A saw e             # A has a direct view of event e
A saw B             # A has seen an event that B took part in
```

- An untimed formula means "at the time of the check".
- Facts that no action can change never need a time.
- A changeable fact of **another world** must say `at`.

---

## 8. Worlds

A file with no `world` is a single world. A story is usually two:

```
world Tale
  ...

world Reading about Tale                 # Tale's names are visible here
  agent Narrator sees all of Tale        # omniscient narrator
  agent Reader
  ...
```

- `about` makes the other world's names visible, and its agents know that world's rules.
- `tell(Narrator, Reader, Tale.start)`: an all-seeing narrator tells how things stood at the start. (A bare `start` means the frame world's own start.)
- `agent Narrator is Tale.Sheppard` creates a first-person narrator. It starts with Sheppard's beliefs at `Tale.end`. The general form is `is <agent> at <time>`, which time travel also uses (section 12). It can lie, or narrate partial views (*The Murder of Roger Ackroyd*).
- Worlds can nest further, for stories within stories.

---

## 9. Libraries

```
use space                          # built in
use "lib/court.ken"                # a file, relative to the model
use "lib/court.ken" as law         # choose the prefix
```

- **std** (below) is in every world without a prefix. Every other library's names are reached through its prefix: `space.go`, `law.testify`.
- A library may declare types, facts, actions, rules and `invariant:` blocks. It may `use` other libraries; their names get both prefixes. It can't declare agents, worlds, a timeline, `given` or time travel.
- Names a library uses without declaring belong to the model that uses it. Ken reports a type the model fails to supply.
- `use` at the top of a file applies to every world; inside a world, to that world only.
- `invariant:` is `expect throughout start .. end`.
- **Sayings**: any action whose first parameter is an agent (the speaker) and which has an untyped parameter called `content` is testimony: people trust it as they trust `tell`, and the honesty rules apply.
- **space** (built in): `fact at(Agent): Place`, `fact distance(Place, Place): Int = 0`, and `action go(x, to)`, seen by those at both ends. It turns on the travel check (section 5).

## 9a. std (built in)

```
fact honest(Agent): bool = true

action tell(x: Agent, y: Agent, content)     # content: a formula, or an event view
  needs:   honest(x) => x believes content
  seen by: x, y

action announce(x: Agent, content)
  needs:   x knows content
  seen by: everyone
```

- **Telling about events.** You can only tell about an event you have a view of. `tell(x, y, e as seen by A)` conveys A's view, and the listener adopts it as their own view of e. Honesty requires x to believe that A saw it that way. That makes focalised narration honest even when A was wrong.
- **Partial views are true.** `kill(B, C)` as a view of `attack(C, D) then kill(B, C)` is incomplete, not false. Wrong conclusions drawn from it are the agent's own.

---

## 10. Checks

```
expect at e4: ...
expect before e2: ...
expect throughout ch1 .. ch6: ...
```

The checker also raises errors by itself for:
- a failed `needs`, including an honest agent telling what they don't believe
- a `because` on an event that the actor doesn't believe just before it
- a conclusion resting on an event the person never saw or heard of, or on a belief they don't hold
- an unresolved belief conflict
- telling about an event the teller never saw or heard of
- a changeable fact from another world used without `at`
- `so that φ` when the actor doesn't want φ
- clock times that run backwards, and (with `use space`) travel faster than the roads allow
- an `invariant:` that stops holding
- `saw`, `wants` or `suspects` nested inside someone's beliefs

It warns when an actor knowingly undoes something they want with no `because` or `so that`, and when a conclusion has no `because`. It notes a plan (`so that`) that hasn't worked yet, and a watcher who notices a change.

### Questions (command line)
- `ken why FILE EVENT "A believes φ"`: each sighting and conclusion of A's up to EVENT is taken away in turn and the world re-run; those without which the belief goes are "needed".
- `ken who FILE EVENT "φ"`: for each agent, knows / believes wrongly / believes the opposite / could deduce (`deducible by`) / doesn't know.
- `ken whatif FILE --drop E` or `--move E --after F`: the difference in Ken's report.
- `ken suggest FILE`: for each failing expectation, single events inserted just before its time that make it hold with fewer errors. Candidates are `tell`/`announce` of the fact-level parts of the expectation, and every instance of the world's actions.
- `ken timeline FILE [--html OUT]`: every agent's belief about every relevant fact at every step.
- `ken mind FILE AGENT [--at EVENT]`: one agent at every step (or one): facts known, believed wrongly, unsure (with the possible values), or contradictory; suspicions, wants and conclusions; what the event looked like to them; what they think each other agent believes, shown where it differs from their own view or from what that agent really believes; and, for a reader, what they believe about the tale. Without `--at`, the start in full and then the changes. Uses the explicit engine.
- `--json` on any command: one JSON object on stdout. `check` gives `ok`, counts and `diagnostics` (level, line, world, at, message); `mind` gives `steps` with `knows`, `wrong`, `unsure`, `contradictory`, `suspects`, `wants`, `concludes`, `thinks_others`, `about` and `changes`; `timeline` gives `facts`; the others give `text`. Failures give `error`.

---

## 11. Keywords (the whole language)

| Group | Keywords |
|---|---|
| Structure | `world` `about` `revises … from` `given` `agent` `is … at` `#` (segment) `sees all of` `type` `fact` `action` `rule` `private` `timeline` `start` `end` `expect` |
| Actions | `needs` `effect` `seen by` `(A, B) …` `every … where` `everyone` `as` `hiding` `secretly` `then` `for … in` |
| Rules | `after` `sees` `for every` `when` `do` |
| Belief | `concludes` `because` `despite` `suspects` `forgets` `watches` `no longer watches` `wants` `no longer wants` `so that` |
| Formulas | `knows` `believes` `whether` `saw` `wants` `suspects` `common knowledge among` `deducible by` `possible for` `all` `some` `in` `not` `and` `or` `=>` `<=>` |
| Time | `at` `before` `throughout` `@` `time travel:` `overwrite` `branching` `fixed` `allow bootstrap` |
| Libraries | `use NAME` `use "file.ken"` `as` `invariant:` |
| Seeing | `secretly except … and …` `may happen unseen` |

## 12. Time travel

The model needs three additions: segments, revised worlds, and a choice of which history is real.

### Segments: one person, several bodies

A person who travels becomes a new **segment**. `Ada#1` is the original and `Ada#2` is the one who has travelled. Each segment is a separate agent with its own beliefs.

- `agent Ada#2 is Ada#1 at e9`: the new segment starts with exactly what Ada#1 believed at e9.
- Plain `Ada` means the only segment present. If two are present, it is an error ("ambiguous").
- **Others see the person, not the segment.** By default a view names `Ada`, so an observer cannot tell which Ada they saw. A logician keeps both possibilities open. Use `as` to make an observer mistake one segment for another explicitly.

### Revised worlds: history rewritten

```
world Loop2 revises Loop1 from e3
```
Loop2 contains everything in Loop1 (declarations, `start`, and events up to and including e3), then continues with its own timeline. Chains are allowed: `Loop3 revises Loop2 from …`.

### Which history is real

Declare it once per file:

| Declaration | Meaning | Example stories |
|---|---|---|
| `time travel: overwrite` (default) | Revisions must form a single chain. The last world is the real history. | Primer, *Back to the Future* |
| `time travel: branching` | Every world is real. Revisions may form a tree. | Multiverse stories |
| `time travel: fixed` | No revisions. Travellers arrive earlier in the same world, and the loop must be self-consistent. | *12 Monkeys*, *Predestination* |

- Under `overwrite`, a top-level formula without a world name refers to the real history.
- Under `branching`, a formula must name its world.
- Under `fixed`, the checker verifies that the loop closes: what the arriving segment starts with equals what the departing segment ends with.

### Checks added

- **Bootstrap paradox** (error): a belief whose chain of sources loops back on itself without ever starting from an observation. It is common in `fixed` stories. Silence it with `allow bootstrap`.
- **Memory drift** (warning): a segment believes something about a future event that its current world has changed. This is often the point of the story, so it's reported rather than treated as an error.
- **Meeting yourself**: write it as an ordinary `expect`, e.g. `expect throughout start .. end: not (Ada#1 saw Ada#2)`.

### Example: The Box (Primer-style, overwrite)

```
time travel: overwrite

world Loop1
  agent Ada, Ben
  type Horse = Swift | Slow
  fact winner: Horse
  fact rich(Agent): bool = false

  action race(h: Horse)                    # h is the winner
    needs:   h = winner                    # watchers learn the winner from this
    seen by: everyone
  action bet(x: Agent, h: Horse)
    effect:  rich(x) = (h = winner)
    seen by: x
  action enter_box(x: Agent)
    seen by: x

  timeline:
    start:
      winner = Swift
      seen by: every a hiding winner
    e1: bet(Ben, Slow)
    e2: race(Swift)
    e3: enter_box(Ada)                     # Ada#1's segment leaves Loop1

world Loop2 revises Loop1 from start       # history restarts after start
  agent Ada#2 is Loop1.Ada at e3           # she remembers the race

  action arrive(x: Agent)
    seen by: x

  timeline:
    a1: arrive(Ada#2)
    a2: tell(Ada#2, Ben, winner = Swift)   # Ben sees "Ada", not which one
    a3: bet(Ben, Swift) because Ben believes winner = Swift
    a4: race(Swift)

  expect at a2:
    Ada#2 knows winner = Swift             # learned at Loop1.e2: her past, the world's future
    not (Ada#1 believes winner = Swift)
    Ben believes winner = Swift            # he took it as advice from plain "Ada"
  expect throughout start .. end:
    not (Ada#1 saw Ada#2)

expect at end:                             # the real history (Loop2)
  rich(Ben)
```

### Example: a bootstrap error (fixed)

```
time travel: fixed
agent Ada
agent Ada#2 is Ada#1 at e9
fact code: Int                             # actions as in The Box

timeline:
  e1: arrive(Ada#2)
  e2: tell(Ada#2, Ada#1, code = 4417)      # where did Ada#2 learn the code?
  e9: enter_box(Ada#1)                     # ...from herself at e2

# checker: error: bootstrap. "code = 4417" has no origin outside the loop.
#          Add "allow bootstrap", or give someone a real observation of the code.
```

---

## Examples

### Sally–Anne

```
agent Sally, Anne
type Place = basket | box
fact marble: Place
fact present(Agent): bool = true

action put(who: Agent, to: Place)
  needs:   present(who)
  effect:  marble = to
  seen by: every a where present(a)

action leave(who: Agent)
  effect:  present(who) = false
  seen by: every a where present(a)

action enter(who: Agent)
  effect:  present(who) = true
  seen by: who, every a where present(a)

timeline:
  start:
    marble = basket
    seen by: Sally, Anne
  1: leave(Sally)
  2: put(Anne, box)          # Sally is absent, so she doesn't see this
  3: enter(Sally)

expect at 3:
  Sally believes marble = basket
  Anne knows marble = box
  Anne knows (Sally believes marble = basket)
```

### Cheryl's Birthday

```
agent Albert, Bernard, Reader : logician
agent Cheryl
type Month = May | June | July | August
type Day = 14 .. 19
type Date = (month: Month, day: Day)
fact birthday: Date in
  May 15, May 16, May 19, June 17, June 18,
  July 14, July 16, August 14, August 15, August 17

timeline:
  start:
    birthday = July 16
    seen by: Cheryl
    seen by: Albert  hiding birthday.day
    seen by: Bernard hiding birthday.month
    seen by: Reader  hiding birthday
  1: announce(Albert, not (Albert knows birthday)
                      and Albert knows not (Bernard knows birthday))
  2: announce(Bernard, Bernard knows birthday)
  3: announce(Albert, Albert knows birthday)

expect at 3:
  Albert knows birthday
  Bernard knows birthday
  Reader knows birthday = July 16
```

### Blue Eyes

```
given n, blue                            # e.g. n = 5, blue = 3

agent Islander[1..n] : logician
agent Guru
type Colour = blue | brown
fact eyes(Islander): Colour
fact gone(Islander): bool = false

action leave(i: Islander)
  needs:   not gone(i)
  effect:  gone(i) = true
  seen by: everyone

action night(k: Int)
  seen by: everyone

rule leaving:
  after night(k), for every Islander i:
    when i knows eyes(i) and not gone(i):
      do leave(i)

timeline:
  start:
    eyes(i) = blue  for i in 1 .. blue
    eyes(i) = brown for i in blue+1 .. n
    seen by: Guru
    seen by: every Islander i hiding eyes(i)
  speech: announce(Guru, some i in Islander: eyes(i) = blue)
  night(k) for k in 1 .. blue+1

expect at start:
  not common knowledge among Islander: some i in Islander: eyes(i) = blue
  blue >= 2 => all j in Islander: j knows (some i in Islander: eyes(i) = blue)
expect before night(blue):
  all i in Islander: not gone(i)
expect at night(blue):
  all i in Islander: gone(i) <=> eyes(i) = blue
expect at night(blue+1):
  all i in Islander: gone(i)             # the brown-eyed work it out a night later
```

### The Defender: a tale and its telling

```
world Tale
  agent A, B, C, D
  fact good(Agent): bool
  fact plotting(Agent): bool = false
  fact alive(Agent): bool = true

  action attack(x: Agent, y: Agent)
    seen by: x, y
  action kill(x: Agent, y: Agent)
    effect:  alive(y) = false
    seen by: x, y
  action sneak_out(x: Agent)
    seen by: x
  action refuse_help(x: Agent, y: Agent)
    seen by: x, y

  timeline:
    start:
      good(B) = true
    e1: attack(C, D) then kill(B, C)
          seen by: B, C, D
          seen by: A as kill(B, C)
          A concludes not good(B) because e1
    e2: sneak_out(B)                     # B is really guarding D
          seen by: B, A secretly
          A concludes plotting(B) because e2 and not good(B)
    e3: refuse_help(A, B) because A believes plotting(B)
    e4: tell(D, A, e1)                   # D gives A the full view of e1
          # A's view of e1 grows, so "not good(B)" is retracted,
          # and so is "plotting(B)", which rested on it.
          A concludes good(B) because e1
          # If A were stubborn, write instead:
          #   A concludes not good(B) because e1 despite e4

world Reading about Tale
  agent Narrator sees all of Tale
  agent Reader

  timeline:
    ch1: tell(Narrator, Reader, e1 as seen by A)
           Reader concludes not good(B) because e1     # source: the event, not the telling
    ch3: tell(Narrator, Reader, e2)
    ch4: tell(Narrator, Reader, e3)
    ch7: tell(Narrator, Reader, e4)
           Reader concludes good(B) because e1

  expect throughout ch1 .. ch4:
    Reader believes not good(B)          # the misdirection works
    possible for Reader: good(B)         # and the twist will be fair
  expect at ch7:
    Reader knows good(B)
    (A believes good(B)) at e4
```

---

## Open questions (need your judgement or real use)

1. **Mixed modes**: how a `person` models a `logician`, and the other way round. Proposal: each models the other in its own mode.
2. **Unseen events for logicians**: v0.4 logicians assume nothing happened that they didn't see. A *suspicious* logician would consider hidden events possible. Worth adding? It's costly.
3. **Durations and places**, for "two places at once". Not in v1. It can already be approximated with a `location` fact and `needs`.
4. **Probability**: not in v1.
5. **Recognising segments**: when can an observer tell `Ada#1` from `Ada#2`? Examples: a visible injury, or knowing travel exists. Proposal for now: only through an explicit `as` view, or a `concludes`.
