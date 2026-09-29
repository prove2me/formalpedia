-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR7.reciprocal_successive_ratio_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T00:49:47.239812+00:00
-- url     : https://prove2.me/submissions/1e5280c8-5229-4909-a16d-713b3a89a05c

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR7_RealTail
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR7_strictMono_nat_cast_tendsto_atTop
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

namespace ErdosProblems.Erdos243.PaperCompleteR7
open Filter
open scoped BigOperators
end ErdosProblems.Erdos243.PaperCompleteR7

open Filter
open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos243 in
open ErdosProblems.Erdos243.PaperCompleteR7 in
theorem solution
    (a : ℕ → ℕ) (ha : StrictMono a) (hpos : ∀ n, 0 < a n)
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2)
      atTop (nhds 1)) :
    Tendsto (fun n ↦ (1 / (a (n + 1) : ℝ)) / (1 / (a n : ℝ)))
      atTop (nhds 0) := by
  have hinv : Tendsto (fun n ↦ (a n : ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (strictMono_nat_cast_tendsto_atTop a ha hpos)
  have hq : Tendsto (fun n ↦ (a n : ℝ) ^ 2 / (a (n + 1) : ℝ))
      atTop (nhds 1) := by
    simpa only [inv_div, inv_one] using hgrowth.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  have hm := hq.mul hinv
  have hlim : Tendsto
      (fun n ↦ (a n : ℝ) ^ 2 / (a (n + 1) : ℝ) * (a n : ℝ)⁻¹)
      atTop (nhds 0) := by simpa only [one_mul] using hm
  apply hlim.congr'
  exact Filter.Eventually.of_forall fun n ↦ by
    have h0 : (a n : ℝ) ≠ 0 := by exact_mod_cast (hpos n).ne'
    have h1 : (a (n + 1) : ℝ) ≠ 0 := by exact_mod_cast (hpos (n + 1)).ne'
    field_simp [h0, h1]
    <;> ring
