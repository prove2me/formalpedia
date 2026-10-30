-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_TernaryTreeBasic
-- name    : AnalyticCombinatorics_Ch7_SingularityApp_TernaryTreeBasic
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-28T12:09:12.643172+00:00
-- url     : https://prove2.me/theorems/43f71f1e-5833-4806-ac96-e6cade7de574
-- title:
--   Ternary Tree Basic
-- statement:
--   The mathematical objects and operations are specified by the following source definitions.
--
--   ```lean
--   def TernaryTreeOfSize (n : ℕ) : Type :=
--     {t : TernaryTree // internalSize t = n}
--   ```
--
--   ```lean
--   inductive TernaryTree where
--     | leaf : TernaryTree
--     | node : TernaryTree → TernaryTree → TernaryTree → TernaryTree
--     deriving DecidableEq, Repr
--   ```
--
--   ```lean
--   def internalSize : TernaryTree → ℕ
--     | .leaf => 0
--     | .node l m r => internalSize l + internalSize m + internalSize r + 1
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch7/SingularityApp/TernaryTreeBasic.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Full ternary trees: the combinatorial object

This file introduces the genuine combinatorial object underlying the
`ternaryTreeCount` sequence of `TernaryTrees.lean`: an inductive type of full
ternary trees, the number of internal nodes (`internalSize`), the finite type
of trees of a fixed size, and the resulting count `ternaryCount`.

The closed form `ternaryCount n = binom(3n,n)/(2n+1)` is proved (via the
triple-convolution recurrence) in `TernaryTreeRecurrence.lean` and
`TernaryFussCatalan.lean`, where it is also connected to the banked
`ternaryTreeCount`.
-/

namespace AnalyticCombinatorics.Ch7.SingularityApp.TernaryTreeNS

/-- A full ternary tree: either a leaf, or an internal node with three
ordered children. -/
inductive TernaryTree where
  | leaf : TernaryTree
  | node : TernaryTree → TernaryTree → TernaryTree → TernaryTree
  deriving DecidableEq, Repr

/-- The number of internal (non-leaf) nodes of a full ternary tree. -/
def internalSize : TernaryTree → ℕ
  | .leaf => 0
  | .node l m r => internalSize l + internalSize m + internalSize r + 1

@[simp] lemma internalSize_leaf : internalSize .leaf = 0 := rfl

@[simp] lemma internalSize_node (l m r : TernaryTree) :
    internalSize (.node l m r) =
      internalSize l + internalSize m + internalSize r + 1 := rfl

/-- The full ternary trees with exactly `n` internal nodes. -/
def TernaryTreeOfSize (n : ℕ) : Type :=
  {t : TernaryTree // internalSize t = n}

end AnalyticCombinatorics.Ch7.SingularityApp.TernaryTreeNS


