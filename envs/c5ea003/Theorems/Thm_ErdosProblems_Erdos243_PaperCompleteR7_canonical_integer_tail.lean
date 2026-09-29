-- Prove2me | Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR7_canonical_integer_tail
-- name    : ErdosProblems.Erdos243.PaperCompleteR7.canonical_integer_tail
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-25T00:50:47.854098+00:00
-- url     : https://prove2.me/theorems/b02a02c1-97dc-4656-8e10-ee8059c8da80
-- title:
--   Lean source theorem: canonical_integer_tail
-- statement:
--   For a positive integer sequence whose reciprocal series sums to the rational p/q, the canonical natural numerator C and denominator D are positive, satisfy C(n+1)+D(n)=a(n)C(n) and D(n+1)=a(n)D(n), and obey C(n)=D(n) times the reciprocal-series tail from n.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR7/CanonicalState.lean#L101-L159
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

theorem ErdosProblems.Erdos243.PaperCompleteR7.canonical_integer_tail
    (a : ℕ → ℕ) (ha : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ))) :
    let C := canonicalNaturalNumerator a p q
    let D := canonicalDenominator a q
    (∀ n, 0 < C n) ∧ (∀ n, 0 < D n) ∧
    (∀ n, C (n + 1) + D n = a n * C n) ∧
    (∀ n, D (n + 1) = a n * D n) ∧
    (∀ n, (C n : ℝ) = (D n : ℝ) * realTail (fun k ↦ 1 / (a k : ℝ)) n) := by sorry
