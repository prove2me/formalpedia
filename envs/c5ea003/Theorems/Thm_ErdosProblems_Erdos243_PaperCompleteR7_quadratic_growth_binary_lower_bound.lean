-- Prove2me | Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR7_quadratic_growth_binary_lower_bound
-- name    : ErdosProblems.Erdos243.PaperCompleteR7.quadratic_growth_binary_lower_bound
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-25T00:50:45.246225+00:00
-- url     : https://prove2.me/theorems/8228e2d5-b463-42fa-8aec-be10f27d6dd1
-- title:
--   Lean source theorem: quadratic_growth_binary_lower_bound
-- statement:
--   For a strictly increasing positive integer sequence with a(n+1)/a(n)² tending to one, there is an index N such that a(N+k)≥2·2^(2^k) for every k.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR7/QuantitativeTail.lean#L129-L170
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1-L58
--   Paper's AI-assistance disclosure: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/paper-house-style.sty#L180-L188
--   Original Erdős problem and Koizumi prior work are distinguished in the paper: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L57-L110

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR7_RealTail
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR7_CanonicalState
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
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
# The quantitative canonical-tail lemma

Compiled candidates for the whole long-record `res:tailratio`.
The O(1/a_n) conclusion has an explicit eventual constant 16.  The growth
bound is first proved as an exact binary-power inequality, and then
converted to the exponential notation of the paper.
-/


open Filter

open ErdosProblems.Erdos243.PaperCompleteR7

theorem ErdosProblems.Erdos243.PaperCompleteR7.quadratic_growth_binary_lower_bound
    (a : ℕ → ℕ) (ha : StrictMono a) (hpos : ∀ n, 0 < a n)
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2)
      atTop (nhds 1)) :
    ∃ N, ∀ k : ℕ, 2 * (2 : ℝ) ^ ((2 : ℕ) ^ k) ≤ (a (N + k) : ℝ) := by sorry
