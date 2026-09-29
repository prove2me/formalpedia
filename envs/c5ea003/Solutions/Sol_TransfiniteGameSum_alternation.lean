-- Prove2me | solution 1 for TransfiniteGameSum.alternation
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T01:12:27.809138+00:00
-- url     : https://prove2.me/submissions/fc392775-75a1-4392-86bb-2cf2d172720a

-- Sol generated from MachineLearning/TransfiniteGameSum.lean
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




/-- A losing position is exactly one all of whose moves lead to winning positions. -/
theorem notW_iff_all_W (p : P) : ¬ W mv hwf p ↔ ∀ q, mv p q → W mv hwf q := by
  rw [W_fix]; push_neg; rfl

/-- From a losing position every move hands the opponent a winning position. -/
theorem not_W_all_W (p : P) (h : ¬ W mv hwf p) : ∀ q, mv p q → W mv hwf q :=
  (notW_iff_all_W mv hwf p).1 h



/-! ## The disjunctive sum -/










/-! ## Determinacy (Zermelo) and the strategic reading of the flagship -/




theorem optMove_spec (x : P) (h : W mv hwf x) :
    mv x (optMove mv hwf x) ∧ ¬ W mv hwf (optMove mv hwf x) := by
  unfold optMove; rw [dif_pos h]; exact Classical.choose_spec (W_has_move mv hwf x h)



@[simp] theorem traj_succ (o p n) :
    traj mv hwf o p (n + 1) = step mv hwf o (traj mv hwf o p n) := rfl

theorem step_W (o) (x : P) (h : W mv hwf x) :
    mv x (step mv hwf o x) ∧ ¬ W mv hwf (step mv hwf o x) := by
  unfold step; rw [if_pos h]; exact optMove_spec mv hwf x h

theorem step_notW (o) (x : P) (hnW : ¬ W mv hwf x) (hnT : ¬ Terminal mv x)
    (ho : Legal mv o) : mv x (step mv hwf o x) ∧ W mv hwf (step mv hwf o x) := by
  unfold step; rw [if_neg hnW]
  exact ⟨ho x hnT, not_W_all_W mv hwf x hnW _ (ho x hnT)⟩







/-! ## The countdown game and the contrarian disproofs -/

open Countdown

open TransfiniteGameSum










open TransfiniteGameSum in
theorem solution(o : P → P) (ho : Legal mv o) (p : P) :
    ∀ n, (∀ k, k < n → ¬ Terminal mv (traj mv hwf o p k)) →
      (W mv hwf (traj mv hwf o p n) ↔ (Even n ↔ W mv hwf p)) := by
  intro n
  induction n with
  | zero => intro _; show W mv hwf p ↔ (Even 0 ↔ W mv hwf p); simp
  | succ n ih =>
    intro hbelow
    have hbn : ∀ k, k < n → ¬ Terminal mv (traj mv hwf o p k) :=
      fun k hk => hbelow k (Nat.lt_succ_of_lt hk)
    have hWn := ih hbn
    have hnT : ¬ Terminal mv (traj mv hwf o p n) := hbelow n (Nat.lt_succ_self n)
    rw [traj_succ]
    by_cases hW : W mv hwf (traj mv hwf o p n)
    · have h2 : ¬ W mv hwf (step mv hwf o (traj mv hwf o p n)) := (step_W mv hwf o _ hW).2
      have hpq : (Even n ↔ W mv hwf p) := hWn.1 hW
      have hpar : Even (n + 1) ↔ ¬ Even n := Nat.even_add_one
      tauto
    · have h2 : W mv hwf (step mv hwf o (traj mv hwf o p n)) :=
        (step_notW mv hwf o _ hW hnT ho).2
      have hpq : ¬ (Even n ↔ W mv hwf p) := fun h => hW (hWn.2 h)
      have hpar : Even (n + 1) ↔ ¬ Even n := Nat.even_add_one
      tauto
