-- Prove2me | Theorems.Thm_TransfiniteGameSum_alternation
-- name    : TransfiniteGameSum.alternation
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:53:49.125229+00:00
-- url     : https://prove2.me/theorems/340378b4-ce89-4ad7-ba89-67f518531338
-- title:
--   Alternation invariant.
-- statement:
--   **Alternation invariant.**
--
--   ```lean
--   theorem TransfiniteGameSum.alternation(o : P → P) (ho : Legal mv o) (p : P) :
--       ∀ n, (∀ k, k < n → ¬ Terminal mv (traj mv hwf o p k)) →
--         (W mv hwf (traj mv hwf o p n) ↔ (Even n ↔ W mv hwf p)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/TransfiniteGameSum.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/TransfiniteGameSum.lean#L205

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










/-! ## Determinacy (Zermelo) and the strategic reading of the flagship -/

theorem TransfiniteGameSum.alternation(o : P → P) (ho : Legal mv o) (p : P) :
    ∀ n, (∀ k, k < n → ¬ Terminal mv (traj mv hwf o p k)) →
      (W mv hwf (traj mv hwf o p n) ↔ (Even n ↔ W mv hwf p)) := by sorry
