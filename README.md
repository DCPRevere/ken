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

## What the checker catches

- An event whose precondition is false (Sally moves the marble while she is out of the room).
- A character acting `because` of a belief they don't hold at that moment.
- A conclusion drawn from an event the character never saw or heard of.
- Someone telling about an event they never witnessed.
- An honest character saying something they don't believe.
- A character whose observations contradict their beliefs.
- Unfair twists: `possible for Reader: …` fails when what the reader was shown rules out the truth.
- Time loops: bootstrap paradoxes (knowledge with no origin outside the loop), and memory drift.
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

`tests/fail/` holds stories with deliberate holes, each naming the error it should produce. Run everything with `cargo test`.

## How it works

- **Two engines.** `--engine auto` (the default) uses a **symbolic engine** when every event after `start` is public. It stores the possible worlds as one BDD and computes "a knows φ" as ∀(what a can't see).(θ → φ). Anything else falls back to the **explicit engine**, which lists the worlds. A test checks that both engines give identical output on Blue Eyes variants of every size up to 7. Force either with `--engine explicit|symbolic`. The BDD library uses complement edges, garbage collection and a one-pass "everyone still can't tell" operation (∧ᵢ ∀xᵢ.θ). Tests check that the shortcuts agree with the general symbolic path, and that the symbolic engine agrees with the explicit one.
- **Logicians and persons** share the explicit engine: a possible-worlds model updated by *product update* (dynamic epistemic logic). Observers get *views* of events, which can be full, partial, mistaken (`as`), or have parts hidden (`hiding`, `secretly`).
- **Persons** additionally take trusted testimony at face value, and hold author-written conclusions as private belief changes with recorded sources. Retraction replays history without the retracted conclusions.
- **Rules** fire in every possible world, so agents learn from rules that *didn't* fire.
- **Readers** of another world (the tale) hold three-valued beliefs built from what they were told and what they concluded.
- **Fixed time loops** are solved by iterating to a fixed point; knowledge missing from a run where the traveller's own actions are suppressed has no origin, which makes it a bootstrap.

The language specification is in [`docs/spec.md`](docs/spec.md) and the design history in [`docs/design-log.md`](docs/design-log.md).

## Limits of this version

- Blue Eyes, on the symbolic engine: 19ms at 100 islanders, 76ms at 200 (0.6s for the full night-by-night test file), 16s at 500.
- Stories with private views, conclusions or testimony use the explicit engine, which lists worlds. It manages around 12–14 agents with hidden facts.
- Only facts that author code reads vary between worlds, which keeps models small. A fact that is read must be given a value at `start` or have a default.
- A reader's beliefs about another world are one level deep. They cannot hold nested beliefs about the tale's characters' minds, and they use the latest known value of each fact.
- `φ at e` is evaluated at the top level, not inside another agent's beliefs.
- Rule-triggered actions do not trigger further rules.
- Logicians assume nothing happened that they didn't see.
- Within a world, telling someone about a past event updates their memory of that event (used for sources and retraction), not their beliefs about facts.
- A time traveller brings beliefs about facts that never change, plus memories of events.
