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
