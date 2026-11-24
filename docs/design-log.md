# Ken — revision log

## v0.1 → v0.2
- Removed `audience` and `telling`. The reader and narrator are ordinary agents, and a telling is a second **world** whose events are `tell`s about the first.
- Added time to formulas (`φ at e`). Unchanging facts need no time.
- Collapsed the 11-row observation table into **views**: `seen by: X`, `as <event>`, `hiding <part>`.
- Truthful speech is no longer special. `announce` is an action whose precondition is `x knows content`.
- Dropped `(lie)` and `(lost)`. A lie is just an `expect`. A lost message is an event nobody sees.
- `start` became the first event, so it uses `seen by` like everything else.
- Added `deducible by` and `possible for`. Fair-play checks became generic.
- Persons model other minds through the known `seen by` rules, as Sabre does. Sally–Anne needs this.

## v0.2 → v0.3 (self-review findings)
1. **Bug: second-hand events didn't teach anything.** The reader *believes* `e4` happened but didn't see it, so testimony about `e1` inside `e4` never reached them. Fix: beliefs come from any event the agent **believes happened**, whether seen or told. Testimony is no longer a separate source. There are now 3 sources, not 4.
2. **Bug: the override rule broke the puzzles.** v0.2 said observers don't know about event-level `seen by`. But Blue Eyes and Cheryl *need* everyone to know who saw what. Fix: whoever sees an event knows how everyone else saw it. Added `secretly` for eavesdroppers, the one case where that should not hold.
3. **Bug: when do rule-triggered actions happen?** `at night(k)` was ambiguous about whether the leaving had occurred yet. Fix: triggered actions are part of the triggering event.
4. **Gap: "not seeing is seeing" wasn't defined.** Fix: each possible world produces its own version of an event. An agent drops every world whose version they would have seen differently.
5. **Trust was a world fact that nobody could believe.** Fix: `fact honest(Agent) = true`. A person trusts x unless they believe `not honest(x)`. Distrust is now an ordinary conclusion, and lies are checkable against the truth.
6. **View conflicts were unspecified.** Fix: a new view replaces an old one if it contains it (seeing more of the same event). Otherwise it is a conflict the author must resolve.
7. **`Tale.B` everywhere was noise.** Fix: `world Reading about Tale` makes Tale's names visible, and expects live inside the world they concern.
8. **Inconsistencies:**
   - One-line action forms → block form only.
   - Three quantifier spellings → `all` / `some` in formulas, `every` in selections.
   - `agent X : sees all of Tale` overloaded the mode slot → `agent X sees all of Tale`.
9. **Blue Eyes expects were informal prose** ("nobody leaves before…") → rewritten as formulas. Added `<=>`.
10. **Undeclared types** in Cheryl (`Month`, `Day`) → declared.

## v0.3 → v0.4 (second review)
1. **`clings to` was the only belief verb that wasn't a conclusion.** Folded into conclusions: `A concludes φ because … despite <source>`. Clinging is just a conclusion that names the evidence it ignores. One fewer construct, and the checker can verify that the ignored evidence exists.
2. **`always`** was redundant with `throughout start .. end` → removed. Added the time point `end`.
3. **`parameters`** → `given`, which reads naturally.
4. **Narrator identity** (`is Tale.Sheppard`): semantics stated. The narrator starts with that character's beliefs at `Tale.end`.

## v0.4 → v0.5 (final read-through)
- **Found:** an omniscient, honest narrator telling `e1 as seen by A` looked like a lie. Fixed by stating that a focalised telling conveys *A's view*, and that a partial view is incomplete, not false.
- Keyword table completed (`where`, `everyone`, `is`, `sees all of`, `for … in`).

Stopping here. The remaining open questions need your judgement or real use, not more desk review.

## v0.5 → v0.6 (time travel)
- New principle 8: memory follows the person, not the clock.
- **Segments** (`Ada#2 is Ada#1 at e9`) reuse the narrator's `is … at` form. Others see the person, not the segment, by default.
- **`revises … from`** builds a new world that shares history up to a point.
- **`time travel: overwrite | branching | fixed`**: one switch decides which history is real. The rest of the model is unchanged.
- New checks: bootstrap paradox (error), memory drift (warning). New formula `A saw e` / `A saw B` for "meeting yourself" and alibis.
- Example "The Box" (Primer-style, original) and a bootstrap error case.
- Self-review fixes: the race now reveals the winner through `needs` (seeing an event teaches its preconditions). Replaced the undefined `exists` formula and the removed `always`.

## v0.6 → v0.7 (classic stories as tests)
Writing Othello, Much Ado, Oedipus, Joseph and Rashomon exposed places where persons broke instead of revising. All six fixes follow one idea: **persons revise, logicians don't.**
1. Trust lost is retroactive: concluding `not honest(x)` withdraws x's testimony and what rested on it (Othello, Oedipus).
2. Testimony that contradicts what you know about something fixed is ignored (Hero at the altar).
3. Surprise about something changeable means it changed unseen (the handkerchief in Cassio's room; Hero unveiled).
4. Later conclusions set aside earlier testimony (Don Pedro after Borachio's confession).
5. Conclusions about another's beliefs (`Hero concludes Claudio believes …`).
6. A conflicting account of an event is accepted when the author resolves it with a conclusion, as the spec already said (the shepherd's account of the crossroads).
Also: the contradiction handler now drops the conclusion that actually caused the contradiction, not just the newest.

## v0.7 → v0.8 (closing the gaps)
Everything on the gaps list from v0.7, in one pass:
1. **Motives**: `wants`, `no longer wants`, `so that`. Errors for unwanted purposes; warnings for knowingly undoing your own want; notes for plans that haven't worked.
2. **Seeing**: `secretly except` (the gulling in *Much Ado* now needs no workaround); `may happen unseen` for logicians; `suspects` as a loose belief.
3. **Questions**: `ken why` (counterfactual: remove each source and re-run), `ken who`, `ken whatif`, `ken suggest`.
4. **Space and time**: `@` clock times and `distance`; the checker pins each person's place at the timed events they take part in.
5. **Revision**: one rule, by recency, for conclusions and testimony together. Forgetting facts and events. Announcements count as testimony for persons.
6. **Engine limits**: rules trigger rules; narrators can tell about another world's `start`; `saw`, `wants` and `suspects` inside beliefs are now errors instead of silently wrong answers (`ken-draft`'s first test exposed this).
7. **Tooling**: `ken timeline` (text and HTML), Vim/Neovim support, `scripts/ken-draft`, a warning for `seen by: A, B as …`, multi-line `effect:`, and `at(...)` usable as a fact name.

Not done, on purpose: probabilities (they would need a different engine), attention limits, an LSP server (Vim's quickfix covers inline errors), characters reasoning about travel time.

## v0.8 → v0.9 (libraries)
- `use NAME`, `use "file.ken"`, `use … as x`. Library names are prefixed (`space.go`); names a library doesn't declare are the model's to supply, and a missing type is reported by name.
- `std` is now a real file (`src/lib/std.ken`): `honest`, `tell`, `announce`. Still always loaded, without a prefix.
- Travel moved out of the core: `distance` is gone; the built-in `space` library provides `at`, `distance` and `go`, and switches the travel check on.
- `invariant:` so libraries (and models) can state what must hold at every step.
- A saying is now any action with a speaker and an untyped `content`, not just `tell` and `announce`, so libraries can add their own (`examples/lib/court.ken`).
- Found on the way: people now take public sayings as testimony, which the symbolic engine doesn't model, so it hands such worlds to the explicit engine.

## v0.9 → v1.0 (Master and Commander)
Modelling the film showed wrong models passing. The principle adopted: **the author asserts the psychology; Ken checks the information.** Reasons, conclusions and who is persuaded are the author's to state. Ken checks the character could have held them.
1. **Reasons for acting must be in the actor's head.** `because φ` on an event now means the actor believes φ, unless φ is already about the actor's own mind. Someone else's suspicion, want or sighting is an error. Before, `because Hollom suspects …` let Aubrey act on a suspicion he couldn't know of.
2. **Grounds for conclusions.** Already checked: cited events were seen or heard, and cited beliefs are held. New: a warning for a conclusion with no `because`. Tried and dropped: a check that cited events "bear on" the conclusion through the facts they mention. It flagged 22 sound conclusions (Claudio at the window, Othello's handkerchief), because the link between event and conclusion is usually the character's own reading, which is psychology.
3. **Watching.** `A watches f`: A sees f's value after every step, and a person who expected otherwise notices and assumes an unseen change. The raft now matters: without it, the French captain sees the lights go out.
4. **Appearances.** An action's later `seen by` lines refine earlier ones and may use `as`, so what an action looks like can depend on facts (a disguised ship looks like a whaler). Evaluated per possible world.
5. **Who is who.** No new machinery: roles are agent-valued facts, and `fact captain: Agent in A, B` (already in the parser, now documented) keeps the candidates few. With all 9 agents as candidates the example took 73s; with 3, 1.5s.
6. **Shared views.** `seen by: (A, B, C) hiding x`.

Still open: the watcher's observation is private (others don't know what they saw), and observers named in an appearance can't see through it.

## v1.0 → v1.1 (for agents)
- `ken mind FILE AGENT [--at EVENT]`: what one character has in mind at each step, for writing a scene from their point of view. "What they think others believe" is filtered to the news: where they think someone differs from them, or misjudge what someone believes. Without the filter, a deceived character "thinks" everyone shares each of their mistakes, which buries the one line that matters (the French captain thinks his secret is safe; Aubrey knows).
- `--json` on every command, so an agent can read results without parsing prose.
