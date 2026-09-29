-- Prove2me | Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR7_clearedIntegerNumerator_cast
-- name    : ErdosProblems.Erdos243.PaperCompleteR7.clearedIntegerNumerator_cast
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-25T00:50:31.692418+00:00
-- url     : https://prove2.me/theorems/3492d102-6358-478d-bd65-3edd9aaf7b3a
-- title:
--   Lean source theorem: clearedIntegerNumerator_cast
-- statement:
--   The real cast of the cleared integer numerator equals the canonical denominator times the rational target p/q minus the finite reciprocal sum through index n−1.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR7/CanonicalState.lean#L55-L87
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1-L58
--   Paper's AI-assistance disclosure: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/paper-house-style.sty#L180-L188
--   Original Erdős problem and Koizumi prior work are distinguished in the paper: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L57-L110

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR7_RealTail
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR7_CanonicalState
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fin.Pigeonhole
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Constructing the canonical integer state and its analytic hypotheses

Compiled candidates.  The rational sum is supplied by its explicit
integer numerator p and positive natural denominator q; it is NOT replaced
by an assumed integer-tail representation.

The cleared numerator is an explicit integer finite sum.  Its positivity
is derived from the positive real tail.  All casting, exact natural
recurrences, and normalised-vanishing inputs are then concluded.
-/


open Filter
open scoped BigOperators

open ErdosProblems.Erdos243.PaperCompleteR7

theorem ErdosProblems.Erdos243.PaperCompleteR7.clearedIntegerNumerator_cast
    (a : ℕ → ℕ) (ha : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q) (n : ℕ) :
    (clearedIntegerNumerator a p q n : ℝ) =
      (canonicalDenominator a q n : ℝ) *
        ((p : ℝ) / (q : ℝ) - ∑ j ∈ Finset.range n, 1 / (a j : ℝ)) := by sorry
