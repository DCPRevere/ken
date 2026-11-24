# Ken

**A knowledge engine. It tracks who knows what, and when.**

You describe a world: who is in it, what happens, and who sees each event. Ken works out what everyone knows and believes at every moment, including what they believe about each other, and what they learn from things that *didn't* happen. It then flags anyone who acts on something they couldn't know.

It was built to find plot holes, but it applies wherever who knows what matters: mysteries, puzzles, games, investigations and protocols.

## A taste

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

timeline:
  start:
    marble = basket
    seen by: Sally, Anne
  1: leave(Sally)
  2: put(Sally, box)          # plot hole: Sally isn't there
```

```
$ ken check sally.ken
error sally.ken:20 [@ 2]: put(Sally, box) needs `present(who)`, which is false here
sally.ken: 0 expectation(s) hold, 0 failed; 1 error(s), 0 warning(s)
```

Retractions cascade. In `examples/defender.ken`, A misreads a killing and decides B is evil. When A later learns the full story, Ken retracts everything that rested on the misreading:

```
note [@ e4]: A no longer believes `not good(B)`: e1 now looks like `attack(C, D) then kill(B, C)`
note [@ e4]: A no longer believes `plotting(B)`: it rested on `not good(B)`, which they no longer believe
error [@ e5]: this happens because `A believes plotting(B)`, but that isn't true just before e5
```

## Install and run

Ken is written in Rust and has no dependencies.

```
cargo install --path .
ken check examples/defender.ken
ken check examples/blue_eyes.ken --given n=200,b=100
ken check FILE [--given k=v,...] [--engine auto|explicit|symbolic] [--quiet]
```

## Asking questions

```
$ ken why examples/othello.ken e6 "Othello believes affair"
Othello believes affair at e6, because of:
  e4       Othello saw tell(Iago, Othello, affair)  (needed, line 44)
  e5       Othello saw carry(Cassio)  (not needed on its own, line 45)
  ...
```

| Command | Answers |
|---|---|
| `ken why FILE EVENT "A believes …"` | Which sightings and conclusions a belief rests on. Each is tested by taking it away and re-running the story. |
| `ken who FILE EVENT "…"` | Who knows it, who believes it wrongly, who believes the opposite, and who could work it out from what they've seen. |
| `ken whatif FILE --drop EVENT` | What changes in Ken's report if an event never happened. `--move EVENT --after EVENT` moves it instead. |
| `ken suggest FILE` | For each failing expectation, single events that would make it hold without new errors. |
| `ken timeline FILE [--html OUT]` | Each character's belief about each fact, step by step, with false beliefs marked. `--html` writes a page. |
| `ken mind FILE AGENT [--at EVENT]` | What one character has in their head at each step: what they know, believe wrongly, are unsure of, suspect, want and conclude, what they think others believe, and what they saw. Without `--at` it shows the start, then only what changes. For writing a scene from that character's point of view. |

Every command takes `--json` and then prints one JSON object on stdout (errors too, as `{"error": …}`), for agents. `check`, `mind` and `timeline` give structured fields; the others wrap their text as `{"text": …}`.

```
$ ken mind examples/sally_anne.ken Sally
...
2: put(Anne, box) (Sally didn't see it)
  still thinks marble = basket, but it is now box
```

Editor support for Vim and Neovim (highlighting, and `:make` errors in the quickfix list) is in [`editors/`](editors/README.md). To draft a model from prose, `scripts/ken-draft STORY.txt OUT.ken` asks Claude Code for a first draft, then feeds Ken's errors back until it checks (it needs the `claude` CLI). The instructions it sends are in [`docs/drafting-guide.md`](docs/drafting-guide.md).

## What the checker catches

- An event whose precondition is false (Sally moves the marble while she is out of the room).
- A character acting `because` of something that isn't in their head at that moment. `because fire` means the actor believes there's a fire; someone else's suspicion can't be anyone's reason.
- A conclusion drawn from an event the character never saw or heard of, from a belief they don't hold, or from nothing at all (a warning).
- Someone telling about an event they never witnessed.
- An honest character saying something they don't believe.
- A character whose observations contradict their beliefs.
- Unfair twists: `possible for Reader: …` fails when what the reader was shown rules out the truth.
- Time loops: bootstrap paradoxes (knowledge with no origin outside the loop), and memory drift.
- Motives: acting `so that` something you don't want; acting against your own want, knowingly, with no reason given. A plan that hasn't worked is reported as a note.
- Clocks and travel: an event timed earlier than the one before it, and (with `use space`) anyone who would have to travel faster than the roads allow.
- `invariant:` lines that stop holding at any step.
- `as` or `hiding` that probably covers fewer observers than you meant (a warning).
- Any `expect` you write that doesn't hold.

When a belief's source changes, the checker retracts it and everything resting on it, and reports the cascade as notes.

## Examples

| File | Shows |
|---|---|
| `examples/sally_anne.ken` | False belief; nested belief ("Anne knows Sally believes…") |
| `examples/cheryl.ken` | Learning from statements about knowledge |
| `examples/blue_eyes.ken` | Common knowledge; learning from what *doesn't* happen |
| `examples/blue_eyes_no_guru.ken` | Without the guru, nobody ever leaves |
| `examples/defender.ken` | A misread event, a retraction cascade, a misled reader and a fair twist |
| `examples/the_box.ken` | Primer-style overwritten time travel; doubles; memory drift |
| `examples/bootstrap.ken` | A fixed time loop flagged as a bootstrap paradox |
| `examples/othello.ken` | A lie and a planted clue; trust lost, and everything the liar said withdrawn |
| `examples/much_ado.ken` | A staged misperception, a faked death, eavesdropping, and testimony set aside |
| `examples/oedipus.ken` | Dramatic irony: the audience knows from the start; a prophet disbelieved |
| `examples/joseph.ken` | A misleading coat, a disguise, a dream fulfilled that only one man knows of |
| `examples/rashomon.ken` | Four contradictory witnesses: who must be lying, and what the listener can tell |
| `examples/the_mill.ken` | A locked-room theft: a logician allows for what happened while he was out; times and distances; a lie that doesn't land |
| `examples/master_and_commander.ken` | Ruses at sea: the French watch the lights (a raft keeps them lit), a disguise decides what they see, and mistaken identity (the "surgeon" is the captain) |

`tests/fail/` holds stories with deliberate holes, each naming the error it should produce. Run everything with `cargo test`.

## Libraries

`std` (`honest`, `tell`, `announce`) is in every world, without a prefix. Everything else comes in with `use`:

```
use space                          # built in: space.at, space.go, space.distance
use "lib/court.ken"                # a file, relative to this one: court.swear, court.testify
use "lib/court.ken" as law         # pick the prefix: law.testify
```

A library is an ordinary `.ken` file of types, facts, actions, rules and `invariant:` blocks; it can't declare agents, worlds or a timeline. Its names are reached through its prefix. Names it uses but doesn't declare are the model's to supply: `space` needs your `type Place`, and Ken says so if it's missing. Libraries can use other libraries. A `use` at the top of a file applies to every world; inside a world, to that world only.

Any action whose first parameter is the speaker and which has an untyped `content` parameter counts as testimony, so a library can define its own ways of saying things: [`examples/lib/court.ken`](examples/lib/court.ken) defines sworn testimony, and `examples/rashomon.ken` uses it.

## How it works

- **Two engines.** `--engine auto` (the default) uses a **symbolic engine** when every event after `start` is public. It stores the possible worlds as one BDD and computes "a knows φ" as ∀(what a can't see).(θ → φ). Anything else falls back to the **explicit engine**, which lists the worlds. A test checks that both engines give identical output on Blue Eyes variants of every size up to 7. Force either with `--engine explicit|symbolic`. The BDD library uses complement edges, garbage collection and a one-pass "everyone still can't tell" operation (∧ᵢ ∀xᵢ.θ). Tests check that the shortcuts agree with the general symbolic path, and that the symbolic engine agrees with the explicit one.
- **Logicians and persons** share the explicit engine: a possible-worlds model updated by *product update* (dynamic epistemic logic). Observers get *views* of events, which can be full, partial, mistaken (`as`), or have parts hidden (`hiding`, `secretly`).
- **Persons** additionally take trusted testimony at face value, and hold author-written conclusions as private belief changes with recorded sources. Retraction replays history without the retracted conclusions. Persons also revise:
  - Seeing or hearing something they thought impossible about a fact that can change, they assume it changed while they weren't looking.
  - They ignore testimony that contradicts what they believe about facts that can't change, or that tells them nothing new.
  - Concluding someone is dishonest withdraws everything that person told them, and every conclusion drawn from it.
  - A conclusion that contradicts earlier testimony sets the testimony aside, and drops only those of their own conclusions that no longer fit.
  - A conclusion can be about another agent's beliefs ("Hero concludes Claudio believes…").
- **Revision by recency.** When a person's beliefs clash, Ken drops all of their own conclusions and accepted testimony, then keeps back each one, newest first, while everything still fits. At the same step their own conclusion beats testimony. What can't be kept is reported ("revises: drops …", "sets aside what X told them").
- **Motives.** `A wants φ` holds from the event it's stated at until `A no longer wants φ`. `so that φ` on an event says what the actor means to bring about.
- **Loose beliefs.** `A suspects φ because e` records a suspicion without committing to it. It lapses when its source changes or when A comes to believe the opposite.
- **Forgetting.** `A forgets fact` makes A unsure of the fact's value again. `A forgets e3` drops the memory of the event, and conclusions that rested on it.
- **Watching.** `A watches lamp` means A sees the lamp's value after every step, so A notices it go out without seeing who did it.
- **Appearances.** An action's own `seen by` lines can say what it looks like to some observers, depending on facts: `seen by: every a where disguised(x) and a != x as pass(Cat)`.
- **Who is who.** Roles are agent-valued facts (`fact captain: Agent in Capitaine, Dubois`), so mistaken identity is a false belief about one.
- **Shared views.** `seen by: (Ben, Cat) hiding guilty(Ada)` gives several observers the same view.
- **Secrets that aren't.** `seen by: B secretly except C` means B thinks nobody knows he saw; C knows, and knows that B thinks so.
- **What might have happened.** An action marked `may happen unseen` is one a logician allows might have happened whenever they weren't watching, unless they would have seen it.
- **Rules** fire in every possible world, so agents learn from rules that *didn't* fire. Actions a rule triggers can trigger further rules.
- **Readers** of another world (the tale) hold three-valued beliefs built from what they were told and what they concluded.
- **Fixed time loops** are solved by iterating to a fixed point; knowledge missing from a run where the traveller's own actions are suppressed has no origin, which makes it a bootstrap.

The language specification is in [`docs/spec.md`](docs/spec.md) and the design history in [`docs/design-log.md`](docs/design-log.md).

## Limits of this version

- Blue Eyes, on the symbolic engine: 19ms at 100 islanders, 76ms at 200 (0.6s for the full night-by-night test file), 16s at 500.
- Stories with private views, conclusions, testimony, wants or forgetting use the explicit engine, which lists worlds. It manages around 12–14 agents with hidden facts. `may happen unseen` multiplies the worlds a logician considers at every step they don't see, so keep such actions few.
- Only facts that author code reads vary between worlds, which keeps models small. A fact that is read must be given a value at `start` or have a default.
- A reader's beliefs about another world are one level deep. They cannot hold nested beliefs about the tale's characters' minds, and they use the latest known value of each fact.
- `φ at e`, `A saw e`, `A wants φ` and `A suspects φ` are evaluated at the top level; inside another agent's beliefs they are an error.
- People (not logicians) assume nothing changed unless they see otherwise; when surprised, they assume a change they didn't see. Logicians assume nothing happened that they didn't see, except actions marked `may happen unseen`.
- Characters don't reason about travel time; only the checker does.
- Within a world, telling someone about a past event updates their memory of that event (used for sources and retraction), not their beliefs about facts. Add a conclusion to change their beliefs.
- Each `as`/`hiding`/`secretly` applies to the observer just before it, or to a bracketed group `(A, B)`. Ken warns when a list looks like it meant otherwise.
- Ken checks that a reason or a conclusion's sources were available to the character, not that they are good reasons or good evidence. That is the character's psychology, and the author's call.
- Others don't learn what a watcher saw. Observers named in an appearance take it at face value.
- Agents who saw nothing at `start` consider every value of every hidden fact possible, which can be slow. Give every agent a view of `start`.
- Revision follows fixed rules (recency, then own conclusions over testimony), not a full theory of belief change. There are no probabilities or degrees of belief beyond `suspects`, and no limits on attention.
- `ken why` and `ken timeline` use the explicit engine. `ken suggest` tries at most 400 single-event insertions.
- A time traveller brings beliefs about facts that never change, plus memories of events.
