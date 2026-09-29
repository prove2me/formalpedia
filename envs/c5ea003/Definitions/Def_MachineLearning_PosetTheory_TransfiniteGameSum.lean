-- Prove2me | Definitions.Def_MachineLearning_PosetTheory_TransfiniteGameSum
-- name    : MachineLearning_PosetTheory_TransfiniteGameSum
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T18:53:21.398376+00:00
-- url     : https://prove2.me/theorems/4b22cd07-c017-4f00-9bd8-32c0e34110f7
-- title:
--   Aether Catalog definitions — MachineLearning_PosetTheory_TransfiniteGameSum
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.PosetTheory.TransfiniteGameSum`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/PosetTheory/TransfiniteGameSum.lean by skeleton subtraction
import Mathlib
import Mathlib.Order.GameAdd
/-
Copyright (c) 2026 Harmonic. All rights reserved.

# Disjunctive sums of well-founded impartial games

A position is winning when it has a move to a non-winning position.  The
well-foundedness assumption permits this recursive definition even when the
height of the game tree is transfinite.  The main result is the mirror theorem:
the sum of a game with an identical copy is losing.
-/

namespace TransfiniteGameSum

/-- The predecessor relation associated to a move relation. -/
def ReverseMove {P : Type*} (move : P → P → Prop) : P → P → Prop :=
  fun q p => move p q

/-- Recursive outcome class of a position in a well-founded impartial game. -/
def winning {P : Type*} (move : P → P → Prop)
    (wf : WellFounded (ReverseMove move)) : P → Prop :=
  wf.fix fun p previous => ∃ q, ∃ h : move p q, ¬ previous q h

/-
The recursive outcome equation.
-/

/-
The recursive outcome equation uniquely determines the outcome class.
-/

/-- A move in a disjunctive sum changes exactly one component. -/
def sumMove {P Q : Type*} (left : P → P → Prop) (right : Q → Q → Prop) :
    P × Q → P × Q → Prop :=
  fun p q => Prod.GameAdd (ReverseMove left) (ReverseMove right) q p

/-
Disjunctive sums preserve well-foundedness.
-/
theorem sumWf {P Q : Type*} {left : P → P → Prop} {right : Q → Q → Prop}
    (hl : WellFounded (ReverseMove left)) (hr : WellFounded (ReverseMove right)) :
    WellFounded (ReverseMove (sumMove left right)) := by
  convert hl.prod_gameAdd hr using 1

/-- Outcome class in a disjunctive sum. -/
def sumWinning {P Q : Type*} (left : P → P → Prop) (right : Q → Q → Prop)
    (hl : WellFounded (ReverseMove left)) (hr : WellFounded (ReverseMove right)) :
    P × Q → Prop :=
  winning (sumMove left right) (sumWf hl hr)


/-
Moves in a sum with an empty right component are exactly left moves.
-/

/-
The empty game is a right identity for outcome classes.
-/

/-
Moves in a sum with an empty left component are exactly right moves.
-/

/-
The empty game is a left identity for outcome classes.
-/

/-
Swapping coordinates preserves legal moves in a self-sum.
-/

/-
The outcome of a self-sum is invariant under swapping its components.
-/


/-- The mover has an immediate winning choice exactly when some option is losing. -/
def MoverCanForce {P : Type*} (move : P → P → Prop)
    (wf : WellFounded (ReverseMove move)) (p : P) : Prop :=
  ∃ q, move p q ∧ ¬ winning move wf q

/-- The opponent controls a position when every legal opening hands back a win. -/
def OpponentCanForce {P : Type*} (move : P → P → Prop)
    (wf : WellFounded (ReverseMove move)) (p : P) : Prop :=
  ∀ q, move p q → winning move wf q

/-
Zermelo determinacy for well-founded impartial games.
-/

/-
On the diagonal self-sum, every opening gives the opponent a winning position.
-/

/-- Countdown is the game in which a heap may be replaced by any smaller heap. -/
def countdownMove (m n : ℕ) : Prop := n < m

/-
Countdown is well-founded.
-/

/-
The sharp two-heap Nim outcome theorem.
-/

/-
Two winning components can have a losing sum.
-/

/-
A losing component need not be neutral: only an empty game is neutral.
-/

-- !-- Lab Notes -- !--
/-
Hypothesis: self-sums should admit a rank-independent mirror response, while
arbitrary sums of losing positions may require finer invariants.

Experiment: finite countdown tables through heap size eight exhibited precisely
the off-diagonal winning pattern.  The same response mechanism was then tested
against the abstract recursive outcome equation.

Analysis: the decisive induction is on one component's original move relation,
not on a one-step sum relation.  After an opening move, the mirror response takes
two coordinates to a smaller diagonal, where the induction hypothesis applies.

Critique: losing positions are not interchangeable with empty games.  The
position zero in countdown is losing but contributes legal context when paired
with a nonempty heap; the explicit `(0,1)` example separates these notions.

Synthesis: well-founded recursion, closure under game addition, the transfinite
mirror theorem, and the complete two-heap countdown classification form one
coherent structural account of disjunctive play.
-/

end TransfiniteGameSum


