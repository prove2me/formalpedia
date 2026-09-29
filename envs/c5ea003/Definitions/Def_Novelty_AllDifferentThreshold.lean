-- Prove2me | Definitions.Def_Novelty_AllDifferentThreshold
-- name    : Novelty_AllDifferentThreshold
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:01:46.031249+00:00
-- url     : https://prove2.me/theorems/487af2e7-e59a-4b7e-a1ff-b1070fc7f184
-- title:
--   Aether Catalog definitions — Novelty_AllDifferentThreshold
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.AllDifferentThreshold`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/AllDifferentThreshold.lean by skeleton subtraction
import Mathlib

/-!
# The AllDifferent satisfiability threshold: an enumerative–order-theoretic–chromatic chain

This file develops, as a self-contained chain of results, the sharp satisfiability
threshold of the atomic `AllDifferent` constraint.  An `AllDifferent` block asks for
`m` *demands* (variables) to be assigned pairwise-distinct values drawn from a pool of
`k` *resources* (symbols).  The chain establishes that this constraint sits at a sharp
boundary located exactly at the *balance point* `m = k` ("demands = resources"), and
that the boundary is simultaneously:

* **enumerative**: the proper-assignment count is the falling factorial
  `partitionFn k m = k.descFactorial m` (`partitionFn_eq_card_embedding`);
* **order-theoretic**: satisfiability is a down-closed (monotone) event in the number
  of demands (`satisfiable_downClosed`), with the exact boundary `m ≤ k`
  (`allDifferent_satisfiable_iff`);
* **chromatic**: the constraint is a proper colouring of a complete graph, colourable
  with `k` colours iff `m ≤ k` (`completeGraph_colorable_iff`).

The chain culminates in Sudoku facts: an `n² × n²` grid line sits *exactly* at the
balance point (`sudoku_line_at_balance`), and the closed-form cyclic Latin square
`L(i,j) = i + j` solves the row/column constraints (`cyclic_row_injective`,
`cyclic_col_injective`) yet provably violates a box constraint already at order `n = 2`
(`cyclic_box_not_allDifferent`), showing the box demands are genuinely new constraints.

Each result builds on the previous one, following the falling-factorial partition
function as the analytic order parameter of the transition.
-/

namespace AllDifferentThreshold

open Nat SimpleGraph

/-- The **partition function** of an atomic `AllDifferent` constraint with `m` demands
drawing from `k` resources: the number of proper (injective) assignments, which equals
the falling factorial `k.descFactorial m`. -/
def partitionFn (k m : ℕ) : ℕ := Nat.descFactorial k m









/-! ## Sudoku: sitting exactly on the threshold -/


/-! ## The cyclic Latin square witness and box failure -/

/-- The closed-form **cyclic** assignment `L(i,j) = i + j` on the additive group
`ZMod N`. -/
def cyclic (N : ℕ) (i j : ZMod N) : ZMod N := i + j




end AllDifferentThreshold


