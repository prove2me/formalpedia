-- Prove2me | Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR7_CanonicalState
-- name    : ErdosProblems_Erdos243_PaperCompleteR7_CanonicalState
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-24T19:09:20.949984+00:00
-- url     : https://prove2.me/theorems/848ab360-5b4d-488b-8128-10b1d6f329e4
-- title:
--   Products and numerator-denominator coordinates
-- statement:
--   Defines a prefix product and three integer or natural numerator-denominator expressions for a positive-integer sequence and rational-sum parameters.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR7/CanonicalState.lean#L1-L189
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1-L58
--   Paper's AI-assistance disclosure: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/paper-house-style.sty#L180-L188
--   Original Erdős problem and Koizumi prior work are distinguished in the paper: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L57-L110

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR7_RealTail
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

namespace ErdosProblems.Erdos243.PaperCompleteR7

open Filter
open scoped BigOperators

def prefixProduct (a : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∏ j ∈ Finset.range n, a j

def clearedIntegerNumerator (a : ℕ → ℕ) (p : ℤ) (q n : ℕ) : ℤ :=
  p * (prefixProduct a n : ℤ) -
    ∑ j ∈ Finset.range n, (q : ℤ) * (prefixProduct a n / a j : ℕ)

def canonicalNaturalNumerator (a : ℕ → ℕ) (p : ℤ) (q n : ℕ) : ℕ :=
  (clearedIntegerNumerator a p q n).toNat

def canonicalDenominator (a : ℕ → ℕ) (q n : ℕ) : ℕ :=
  q * prefixProduct a n















end ErdosProblems.Erdos243.PaperCompleteR7


