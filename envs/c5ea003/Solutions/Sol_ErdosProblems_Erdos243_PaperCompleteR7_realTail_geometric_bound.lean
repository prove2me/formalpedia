-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR7.realTail_geometric_bound
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T01:11:20.233915+00:00
-- url     : https://prove2.me/submissions/72cdc79a-fa94-4294-b7d0-44e4ce4d1b2d

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
    (t : ℕ → ℝ) (ht : Summable t) (hpos : ∀ n, 0 ≤ t n)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) (N n : ℕ) (hn : N ≤ n)
    (hstep : ∀ j, N ≤ j → t (j + 1) ≤ r * t j) :
    realTail t n ≤ (1 - r)⁻¹ * t n := by
  have hmajor : ∀ k : ℕ, t (k + n) ≤ r ^ k * t n := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        calc
          t (k + 1 + n) = t ((k + n) + 1) := by congr 1 <;> omega
          _ ≤ r * t (k + n) := hstep (k + n) (by omega)
          _ ≤ r * (r ^ k * t n) := mul_le_mul_of_nonneg_left ih hr
          _ = r ^ (k + 1) * t n := by rw [pow_succ]; ring
  have hg : HasSum (fun k : ℕ ↦ r ^ k) ((1 - r)⁻¹) :=
    hasSum_geometric_of_abs_lt_one (by rwa [abs_of_nonneg hr])
  have hgm : HasSum (fun k : ℕ ↦ r ^ k * t n) ((1 - r)⁻¹ * t n) :=
    hg.mul_right (t n)
  have hs : Summable (fun k : ℕ ↦ t (k + n)) := (summable_nat_add_iff n).mpr ht
  calc
    realTail t n ≤ ∑' k : ℕ, r ^ k * t n :=
      hs.tsum_le_tsum hmajor hgm.summable
    _ = (1 - r)⁻¹ * t n := hgm.tsum_eq
