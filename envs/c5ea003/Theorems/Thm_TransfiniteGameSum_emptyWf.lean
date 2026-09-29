-- Prove2me | Theorems.Thm_TransfiniteGameSum_emptyWf
-- name    : TransfiniteGameSum.emptyWf
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:54:04.754661+00:00
-- url     : https://prove2.me/theorems/2ea946a9-cb54-4c4c-8529-931bf5953386
-- title:
--   The empty relation is well-founded.
-- statement:
--   The empty relation is well-founded.
--
--   ```lean
--   theorem TransfiniteGameSum.emptyWf(P : Type*) : WellFounded (ReverseMove (fun _ _ : P => False)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/PosetTheory/TransfiniteGameSum.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/PosetTheory/TransfiniteGameSum.lean#L72

-- Thm stub generated from MachineLearning/PosetTheory/TransfiniteGameSum.lean
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

theorem TransfiniteGameSum.emptyWf(P : Type*) : WellFounded (ReverseMove (fun _ _ : P => False)) := by sorry
