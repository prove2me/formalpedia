-- Prove2me | Theorems.Thm_SymmetryBreakingCost_QTree_card_le_two_pow_depth
-- name    : SymmetryBreakingCost.QTree.card_le_two_pow_depth
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:38:16.934273+00:00
-- url     : https://prove2.me/theorems/5af9da8d-9ef5-4637-9d3e-e300c90390e4
-- title:
--   Adaptive lower bound.
-- statement:
--   **Adaptive lower bound.**  A decision tree of depth `d` can identify at most `2 ^ d`
--   candidates.
--
--   ```lean
--   theorem SymmetryBreakingCost.QTree.card_le_two_pow_depth: ∀ (t : QTree) (S : Finset ℕ), t.Solves S → S.card ≤ 2 ^ t.depth
--     := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/SymmetryBreakingCostAdaptive.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/SymmetryBreakingCostAdaptive.lean#L71

-- Thm stub generated from Novelty/SymmetryBreakingCostAdaptive.lean
import Mathlib
import Definitions.Def_Novelty_SymmetryBreakingCostAdaptive
import Definitions.Def_Novelty_SymmetryBreakingCostFactoring

/-!
# Adaptivity buys nothing: the isolation cost is a decision-tree invariant

The first cycle measured the isolation cost of a *non-adaptive* battery: a fixed tuple of test
integers, all queries chosen in advance.  A natural objection is that an adaptive strategy —
choosing the next test integer after seeing the previous answers — could be cheaper.  It is not.

We model an adaptive strategy as a binary decision tree `QTree`: each internal node carries a
test integer `x`, and the candidate `r` is routed left when `J(x | r) = 1` and right otherwise;
each leaf outputs a guess.  A tree *solves* a candidate set `S` when it outputs `r` on every
`r ∈ S`.

* `QTree.card_le_two_pow_depth` : a tree of depth `d` solves at most `2 ^ d` candidates.
* `QTree.clog_le_depth` : hence every adaptive strategy needs depth at least `⌈log₂ |S|⌉`.
* `QTree.exists_solving_tree` : and `⌈log₂ |S|⌉` is achieved, by the *non-adaptive* battery of
  the first cycle compiled into a complete binary tree.
* `adaptiveCost_isLeast` : the least depth of a solving tree is exactly `Nat.clog 2 S.card`,
  the same number as the non-adaptive cost `isolationCost_isLeast`.

So the `⌈log₂ π(√N)⌉` figure is not an artefact of the non-adaptive model: it is the exact
query complexity of the residue oracle, adaptively or not.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer, cycle 3): adaptivity can only help when answers are *unbalanced*; here
the Chinese remainder theorem makes every answer pattern realisable, so the tree is forced to be
complete and adaptivity gains nothing.

Experiment (Experimenter): exhaustive search over all decision trees of depth `≤ 3` on the
candidate set `{3, 5, 7, 11, 13}` (`|S| = 5`, `⌈log₂ 5⌉ = 3`): no tree of depth `2` separates
the five candidates (each such tree has at most `4` leaves), while the battery `[2, 3, 10]`
compiled into a complete tree of depth `3` does — its answer patterns on `3, 5, 7, 11, 13` are
`(-1,0,1), (-1,-1,0), (1,-1,-1), (-1,1,-1), (-1,1,1)`, pairwise distinct.

Analysis (Analyst): the lower bound is a pure counting induction on the tree — the candidate set
splits into the two subtrees, and `2 ^ a + 2 ^ b ≤ 2 ^ (max a b + 1)`.  The upper bound reuses
the CRT construction verbatim, showing that the two bounds meet.

Critique (Critic): the model must allow *arbitrary* integers at each node, otherwise the lower
bound would be about a restricted strategy class; `QTree.node` carries an unrestricted `ℤ`, and
the routing predicate is the raw Jacobi answer, so no strategy is excluded.
-/

open SymmetryBreakingCost

open Finset
open scoped NumberTheorySymbols


open QTree

theorem SymmetryBreakingCost.QTree.card_le_two_pow_depth: ∀ (t : QTree) (S : Finset ℕ), t.Solves S → S.card ≤ 2 ^ t.depth
  := by sorry
