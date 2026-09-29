-- Prove2me | Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR7_reciprocal_successive_ratio_tendsto_zero
-- name    : ErdosProblems.Erdos243.PaperCompleteR7.reciprocal_successive_ratio_tendsto_zero
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-25T00:32:38.606316+00:00
-- url     : https://prove2.me/theorems/eb0a7dbf-e74e-43eb-8579-9a054074239f
-- title:
--   Lean source theorem: reciprocal_successive_ratio_tendsto_zero
-- statement:
--   For a strictly increasing positive integer sequence with a(n+1)/a(n)² tending to one, the ratio of consecutive reciprocal terms, [1/a(n+1)]/[1/a(n)], tends to zero.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR7/RealTail.lean#L138-L160
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
# Analytic part of the canonical tail bridge

Compiled candidates.  The principal analytic assertion is proved, not
postulated: if positive summable terms have successive ratio tending to
zero, their tail divided by the leading term tends to one.

The final theorem derives normalised vanishing from quadratic growth and
an exact tail representation.  It does NOT claim to have constructed the
canonical integer state, proved its integrality, or obtained the sharper
O(1/a_n) expansion required elsewhere in the papers.
-/


open Filter
open scoped BigOperators

open ErdosProblems.Erdos243.PaperCompleteR7

theorem ErdosProblems.Erdos243.PaperCompleteR7.reciprocal_successive_ratio_tendsto_zero
    (a : ℕ → ℕ) (ha : StrictMono a) (hpos : ∀ n, 0 < a n)
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2)
      atTop (nhds 1)) :
    Tendsto (fun n ↦ (1 / (a (n + 1) : ℝ)) / (1 / (a n : ℝ)))
      atTop (nhds 0) := by sorry
