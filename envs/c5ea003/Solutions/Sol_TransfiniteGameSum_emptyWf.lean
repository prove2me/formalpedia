-- Prove2me | solution 1 for TransfiniteGameSum.emptyWf
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T01:12:28.943335+00:00
-- url     : https://prove2.me/submissions/25e035ce-ae0d-47d3-9b6d-7cbd3ab48271

-- Sol generated from MachineLearning/PosetTheory/TransfiniteGameSum.lean
import Mathlib
import Definitions.Def_MachineLearning_PosetTheory_TransfiniteGameSum
import Mathlib.Order.GameAdd
/-
Copyright (c) 2026 Harmonic. All rights reserved.

# Disjunctive sums of well-founded impartial games

A position is winning when it has a move to a non-winning position.  The
well-foundedness assumption permits this recursive definition even when the
height of the game tree is transfinite.  The main result is the mirror theorem:
the sum of a game with an identical copy is losing.
-/

open TransfiniteGameSum



/-
The recursive outcome equation.
-/

/-
The recursive outcome equation uniquely determines the outcome class.
-/


/-
Disjunctive sums preserve well-foundedness.
-/



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




/-
Zermelo determinacy for well-founded impartial games.
-/

/-
On the diagonal self-sum, every opening gives the opponent a winning position.
-/


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


open TransfiniteGameSum in
theorem solution(P : Type*) : WellFounded (ReverseMove (fun _ _ : P => False)) := by
  exact ⟨fun x => Acc.intro x (fun _ h => False.elim h)⟩
