-- Prove2me | Definitions.Def_Novelty_SymmetryBreakingCostAdaptive
-- name    : Novelty_SymmetryBreakingCostAdaptive
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:44:00.660051+00:00
-- url     : https://prove2.me/theorems/9e2af6ef-7de6-4516-9aa1-a069d717fd0e
-- title:
--   Aether Catalog definitions — Novelty_SymmetryBreakingCostAdaptive
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.SymmetryBreakingCostAdaptive`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/SymmetryBreakingCostAdaptive.lean by skeleton subtraction
import Mathlib
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

namespace SymmetryBreakingCost

open Finset
open scoped NumberTheorySymbols

/-- A binary decision tree of quadratic-residue queries: each node tests one integer against the
candidate and branches on whether the Jacobi symbol is `1`; each leaf outputs a guess. -/
inductive QTree : Type
  | leaf : ℕ → QTree
  | node : ℤ → QTree → QTree → QTree
  deriving Inhabited

namespace QTree

/-- Running a strategy against a candidate `r`. -/
def run : QTree → ℕ → ℕ
  | leaf n, _ => n
  | node x t f, r => if J(x | r) = 1 then run t r else run f r

/-- The number of queries along the longest branch. -/
def depth : QTree → ℕ
  | leaf _ => 0
  | node _ t f => max (depth t) (depth f) + 1

/-- A strategy *solves* `S` when it identifies every candidate of `S`. -/
def Solves (t : QTree) (S : Finset ℕ) : Prop := ∀ r ∈ S, t.run r = r



/-- The complete binary tree of a list of queries, with an arbitrary decoder at the leaves. -/
def full : List ℤ → (List Bool → ℕ) → QTree
  | [], dec => leaf (dec [])
  | x :: xs, dec =>
      node x (full xs fun bs => dec (true :: bs)) (full xs fun bs => dec (false :: bs))

/-- The answer pattern of a candidate against a list of queries. -/
def sigList (xs : List ℤ) (r : ℕ) : List Bool := xs.map fun x => decide (J(x | r) = 1)





end QTree

end SymmetryBreakingCost


