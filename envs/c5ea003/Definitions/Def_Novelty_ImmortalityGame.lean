-- Prove2me | Definitions.Def_Novelty_ImmortalityGame
-- name    : Novelty_ImmortalityGame
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:29:28.694802+00:00
-- url     : https://prove2.me/theorems/7e285c60-2c94-4488-8006-0a995a96834d
-- title:
--   Aether Catalog definitions — Novelty_ImmortalityGame
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.ImmortalityGame`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/ImmortalityGame.lean by skeleton subtraction
import Mathlib

/-!
# Infinite Games Against Death: Immortality Strategies

We formalize a *survival game* between two players:

* **Mortal**, who has bounded ("finite") computational power, and
* **Eternity**, who can run for transfinitely many rounds and wants Mortal dead.

The game is played over transfinitely many rounds indexed by ordinals.  Mortal
must, at each round it survives, produce a fresh *moment* — an internal
configuration witnessing that it is still alive — and these moments must be
strictly increasing (time only moves forward).  The collection of moments Mortal
can ever reach is exactly what its computational power buys it, and it forms a
well-ordered set.

The central quantity is the **survival value** of a game: the order type of the
set of reachable moments.  This is the least ordinal that Mortal *cannot* reach,
i.e. the round at which Mortal is guaranteed to die.

The main results are:

* `mortalForces_iff_le` — Mortal can force survival to round `β` iff `β` is at
  most the survival value.  (A "play of length `β`" is an order embedding of the
  first `β` rounds into the reachable moments.)
* `finiteGame_value` / `mortal_forces_omega` / `omega_is_sharp` — a Mortal with
  purely **finite deterministic** computation (its moments are indexed by `ℕ`,
  order type `ω`) can force *at least* `ω` rounds — it survives every finite
  round `n` — but dies exactly at round `ω`.
* `nondetGame_value` / `mortal_forces_omega_sq` / `omega_sq_is_sharp` — a Mortal
  with **bounded nondeterminism** (its moments are indexed by `ℕ ×ₗ ℕ`, order
  type `ω²`) can force *at least* `ω²` rounds — it survives every round `ω · n` —
  but dies exactly at round `ω²`.
* `value_le_omega_of_embeds_nat` — conversely, *any* Mortal whose reachable
  moments embed into `ℕ` (the hallmark of finite deterministic computation)
  cannot survive past `ω`.  Reaching `ω²` genuinely requires nondeterminism.
* `nondetExt_value` — the general mechanism behind the jump: refining each of a
  game's moments into an `ω`-block of sub-moments multiplies the survival value
  by `ω`.  Applied to the finite game this upgrades `ω` to `ω²`.

## Connection to Infinite Time Turing Machines (ITTMs)

An ITTM runs its tape through transfinite ordinal time, taking limits of cell
values at limit stages.  A *deterministic* ITTM with a finite work alphabet that
must halt (die) traces out a sequence of configurations whose reachable "clock"
values are order-isomorphic to an initial segment of `ω` before the first limit
intervention — matching `finiteGame`.  Allowing a *bounded* amount of
nondeterministic branching at each stage lets the machine reset a bounded
counter across limit stages, stacking `ω`-blocks and reaching clock values up to
`ω²` — matching `nondetGame`.  The ordinals `ω` and `ω²` are precisely the first
two "clockable" milestones one meets when climbing this hierarchy, and the
sharpness results (`omega_is_sharp`, `omega_sq_is_sharp`) pin them down exactly.
-/

namespace ImmortalityGame

open Ordinal

/-- A **survival game**.  `Moment` is the (well-ordered) set of internal
configurations — *moments of being alive* — that Mortal's computational power
allows it to reach.  Each surviving round Mortal must exhibit a strictly larger
moment than in the previous round, so the length of a survivable play is bounded
by the order type of `Moment`. -/
structure SurvivalGame where
  /-- The type of reachable "moments of being alive". -/
  Moment : Type
  /-- Moments are linearly ordered in time. -/
  [linOrd : LinearOrder Moment]
  /-- Time is well-founded: Mortal cannot descend forever, only ascend. -/
  [wo : IsWellOrder Moment (· < ·)]

attribute [instance] SurvivalGame.linOrd SurvivalGame.wo

/-- The **survival value** of a game: the order type of the reachable moments.
This is the least ordinal Mortal cannot reach, i.e. the round of guaranteed
death. -/
noncomputable def SurvivalGame.value (G : SurvivalGame) : Ordinal :=
  Ordinal.type ((· < ·) : G.Moment → G.Moment → Prop)

/-- A **play of length `β`**: a strictly monotone schedule assigning to each of
the first `β` rounds a distinct reachable moment, in increasing order.  Formally
an order embedding of `β`'s rounds into the reachable moments. -/
def SurvivalGame.Play (G : SurvivalGame) (β : Ordinal) : Type :=
  ((· < ·) : β.ToType → β.ToType → Prop) ↪r ((· < ·) : G.Moment → G.Moment → Prop)

/-- **Mortal can force survival to round `β`** if some play of length `β`
exists. -/
def SurvivalGame.MortalForces (G : SurvivalGame) (β : Ordinal) : Prop :=
  Nonempty (G.Play β)





/-! ## The finite deterministic game: Mortal forces `ω` -/

/-- The **finite deterministic** game: Mortal's reachable moments are indexed by
`ℕ`, of order type `ω`.  This models a machine with finite memory whose clock
advances one tick per round. -/
def finiteGame : SurvivalGame where
  Moment := ℕ





/-! ## The bounded-nondeterministic game: Mortal forces `ω²` -/

/-- The **bounded nondeterministic** game: Mortal's reachable moments are indexed
by `ℕ ×ₗ ℕ` (lexicographic), of order type `ω²`.  The major coordinate counts
`ω`-blocks (limit stages survived), the minor coordinate counts ticks within a
block; a bounded nondeterministic reset lets Mortal begin a fresh block. -/
def nondetGame : SurvivalGame where
  Moment := Lex (ℕ × ℕ)






/-! ## Finite computation is genuinely bounded by `ω`

The following converse shows the dichotomy is real: *any* Mortal whose reachable
moments embed order-preservingly into `ℕ` — the defining feature of finite
deterministic computation — cannot survive past `ω`.  Breaking the `ω` barrier
provably requires more than finite computation. -/




/-! ## The refinement mechanism: multiplying survival by `ω`

The general reason bounded nondeterminism upgrades `ω` to `ω²` is a *refinement*:
replacing each moment by a whole `ω`-block of sub-moments (lexicographically, the
old moment being the major coordinate) multiplies the survival value by `ω`. -/

/-- The **`ω`-refinement** of a game: each moment is expanded into an `ω`-indexed
block of sub-moments, ordered lexicographically with the original moment as the
major coordinate. -/
def nondetExt (G : SurvivalGame) : SurvivalGame where
  Moment := Lex (G.Moment × ℕ)



end ImmortalityGame


