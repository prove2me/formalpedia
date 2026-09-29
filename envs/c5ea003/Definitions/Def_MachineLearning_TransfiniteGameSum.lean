-- Prove2me | Definitions.Def_MachineLearning_TransfiniteGameSum
-- name    : MachineLearning_TransfiniteGameSum
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T19:16:09.553868+00:00
-- url     : https://prove2.me/theorems/c19c987a-af83-4023-ab55-05933b6cbd9e
-- title:
--   Aether Catalog definitions — MachineLearning_TransfiniteGameSum
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.TransfiniteGameSum`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/TransfiniteGameSum.lean by skeleton subtraction
import Mathlib
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

namespace TransfiniteGameSum

variable {P : Type*} (mv : P → P → Prop) (hwf : WellFounded (fun q p : P => mv p q))

/-- The **value** of a position: `W p` holds iff the player to move at `p` has a
winning strategy, i.e. there is a move to a position losing for its mover. -/
noncomputable def W : P → Prop :=
  hwf.fix (fun p IH => ∃ q, ∃ h : mv p q, ¬ IH q h)

/-- **Zermelo fixed-point equation.** -/
theorem W_fix (p : P) : W mv hwf p ↔ ∃ q, mv p q ∧ ¬ W mv hwf q := by
  unfold W; rw [WellFounded.fix_eq]
  constructor
  · rintro ⟨q, h, hn⟩; exact ⟨q, h, hn⟩
  · rintro ⟨q, h, hn⟩; exact ⟨q, h, hn⟩

/-- A position is *terminal* when the player to move has no legal move. -/
def Terminal (p : P) : Prop := ¬ ∃ q, mv p q



/-- A winning position has a move to a losing one. -/
theorem W_has_move (p : P) (h : W mv hwf p) : ∃ q, mv p q ∧ ¬ W mv hwf q :=
  (W_fix mv hwf p).1 h


/-! ## The disjunctive sum -/

/-- The **disjunctive sum move relation**: a move picks one component and makes a
legal move there, leaving the other component fixed. -/
def sumMv (a b : P × P) : Prop :=
  (mv a.1 b.1 ∧ a.2 = b.2) ∨ (a.1 = b.1 ∧ mv a.2 b.2)

/-- The disjunctive sum of a well-founded game with itself is well-founded:
no infinite play, exactly `Prod.GameAdd` of the reverse move relation. -/
theorem sumWf (hwf : WellFounded (fun q p : P => mv p q)) :
    WellFounded (fun q p : P × P => sumMv mv p q) := by
  have hga : WellFounded (Prod.GameAdd (fun q p : P => mv p q) (fun q p : P => mv p q)) :=
    WellFounded.prod_gameAdd hwf hwf
  apply Subrelation.wf ?_ hga
  intro q p h
  obtain ⟨p1, p2⟩ := p; obtain ⟨q1, q2⟩ := q
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · simp only at h1 h2; subst h2; exact Prod.GameAdd.fst h1
  · simp only at h1 h2; subst h1; exact Prod.GameAdd.snd h2

/-- The value function of the disjunctive sum game. -/
noncomputable def Wsum (r : P × P) : Prop := W (sumMv mv) (sumWf mv hwf) r







/-! ## Determinacy (Zermelo) and the strategic reading of the flagship -/

/-- A strategy `o` is *legal* if it moves from every non-terminal position. -/
def Legal (o : P → P) : Prop := ∀ x, ¬ Terminal mv x → mv x (o x)


/-- The canonical optimal move at a winning position. -/
noncomputable def optMove (x : P) : P :=
  if h : W mv hwf x then Classical.choose (W_has_move mv hwf x h) else x


/-- One step of play: the analysed player uses `optMove`, the opponent uses `o`. -/
noncomputable def step (o : P → P) (x : P) : P :=
  if W mv hwf x then optMove mv hwf x else o x

/-- The trajectory under the canonical strategy against opponent `o`. -/
noncomputable def traj (o : P → P) (p : P) : ℕ → P
  | 0 => p
  | n + 1 => step mv hwf o (traj o p n)









end TransfiniteGameSum

/-! ## The countdown game and the contrarian disproofs -/

namespace Countdown

open TransfiniteGameSum

/-- Countdown move relation on `ℕ`: from `a` one may move to any smaller `b`. -/
def cmv (a b : ℕ) : Prop := b < a








end Countdown


