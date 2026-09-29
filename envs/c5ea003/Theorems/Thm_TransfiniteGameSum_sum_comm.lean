-- Prove2me | Theorems.Thm_TransfiniteGameSum_sum_comm
-- name    : TransfiniteGameSum.sum_comm
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:54:06.173271+00:00
-- url     : https://prove2.me/theorems/a21aef8a-dc58-4c0c-9131-ec1dc6794b7d
-- title:
--   Commutativity of the sum value.
-- statement:
--   **Commutativity of the sum value.**
--
--   ```lean
--   theorem TransfiniteGameSum.sum_comm(a b : P) : Wsum mv hwf (a, b) ↔ Wsum mv hwf (b, a) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/PosetTheory/TransfiniteGameSum.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/PosetTheory/TransfiniteGameSum.lean#L138

-- Thm stub generated from MachineLearning/TransfiniteGameSum.lean
import Mathlib
import Definitions.Def_MachineLearning_TransfiniteGameSum
/-
# Transfinite Game Theory, Deepened: The Disjunctive Sum of Well-Founded Games

This file **extends** the theory of two-player well-founded (transfinite) games
to their *disjunctive sum* — the fundamental algebraic operation of combinatorial
game theory, in which a move consists of choosing one component and making a legal
move there.  Well-foundedness of the move relation is exactly the statement that no
play lasts forever, while allowing plays of arbitrary transfinite ordinal rank, so
this is a genuine theory of games that can (almost) last forever.

Building on the value function `W` (a position is winning for the player to move
iff there is a move to a losing position — the Zermelo/Sprague–Grundy fixed point),
we prove:

## Main results

* `sumWf` — the disjunctive sum of a well-founded game with itself is again
  well-founded (via `Prod.GameAdd`), so `W` is defined for it.
* `sum_terminal_right` / `sum_terminal_left` — **a terminal (empty) game is a
  neutral element**: adjoining a component with no moves does not change the value.
* `sum_comm` — **the sum is commutative in value**: `W (a,b) ↔ W (b,a)`.
* `diag_loss` — **flagship theorem**: `G + G` is *always* a loss for the player to
  move (`¬ W (a,a)`).  This is the transfinite mirroring / strategy-stealing
  principle: the second player copies the first player's move in the other copy.
* `determinacy` — Zermelo's theorem for well-founded games: the player to move can
  force a win iff the position is winning.  Combined with `diag_loss`, in `G + G`
  the *opponent* has a winning strategy (`¬ MoverWins (a,a)`).

## Contrarian disproofs

* `sum_of_wins_can_lose` — the naive conjecture "the sum of two winning positions
  is winning" is **false**: `1 + 1` in the countdown game is a loss although each
  `1` is a win.
* `p_position_not_neutral` — the conjecture "a losing component can be dropped
  without changing the winner" is **false**: `0 + 1` is a win although `0` is a
  loss and `1` is a win (so a P-position is *not* an absorbing element).

## A concrete instance

`Countdown` is the game on `ℕ` where from `a` one may move to any smaller number
(rank `ω`).  We recompute its value and instantiate the disproofs.
-/


open Classical

open TransfiniteGameSum

variable {P : Type*} (mv : P → P → Prop) (hwf : WellFounded (fun q p : P => mv p q))








/-! ## The disjunctive sum -/

theorem TransfiniteGameSum.sum_comm(a b : P) : Wsum mv hwf (a, b) ↔ Wsum mv hwf (b, a) := by sorry
