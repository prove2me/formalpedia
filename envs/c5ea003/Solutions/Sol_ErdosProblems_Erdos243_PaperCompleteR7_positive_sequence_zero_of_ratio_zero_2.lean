-- Prove2me | solution 2 for ErdosProblems.Erdos243.PaperCompleteR7.positive_sequence_zero_of_ratio_zero
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T22:40:26.986793+00:00
-- url     : https://prove2.me/submissions/0dbaea44-0121-474b-9ae6-2a84d758450d

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
# The original-coordinate bounded-product-defect corollary

Compiled candidates.  This module supplies the analytic error dictionary
rather than assuming bounded centred error.  Finite upper limsup is stated
as eventual boundedness above by a real constant; the finite initial
segment is irrelevant.  Rationality is given by p/q and HasSum.

The proof avoids assuming a pre-existing double-exponential estimate:
P_n/a_n^2 tends to zero by its successive-ratio identity.  This suffices
for the exact two-term error dictionary.
-/


open Filter
open scoped BigOperators

open ErdosProblems.Erdos243.PaperCompleteR7

theorem solution
    (u : ℕ → ℝ) (hu : ∀ n, 0 < u n)
    (hratio : Tendsto (fun n ↦ u (n + 1) / u n) atTop (nhds 0)) :
    Tendsto u atTop (nhds 0) := by
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hratio (1 / 2) (by norm_num)
  have hstep : ∀ n, N ≤ n → u (n + 1) ≤ (1 / 2) * u n := by
    intro n hn
    have hnonneg : 0 ≤ u (n + 1) / u n := div_nonneg (hu _).le (hu _).le
    have hh : u (n + 1) / u n < 1 / 2 := by
      simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg] using hN n hn
    exact (div_le_iff₀ (hu n)).mp hh.le
  have hbound : ∀ k : ℕ, u (k + N) ≤ (1 / 2 : ℝ) ^ k * u N := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        calc
          u (k + 1 + N) = u (k + N + 1) := by congr 1 <;> omega
          _ ≤ (1 / 2) * u (k + N) := hstep _ (by omega)
          _ ≤ (1 / 2) * ((1 / 2 : ℝ) ^ k * u N) :=
            mul_le_mul_of_nonneg_left ih (by norm_num)
          _ = (1 / 2 : ℝ) ^ (k + 1) * u N := by rw [pow_succ]; ring
  have hgeom : Tendsto (fun k : ℕ ↦ (1 / 2 : ℝ) ^ k * u N) atTop (nhds 0) := by
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).mul_const (u N)
  have hshift : Tendsto (fun k : ℕ ↦ u (k + N)) atTop (nhds 0) :=
    squeeze_zero (fun k ↦ (hu (k + N)).le) hbound hgeom
  exact (Filter.tendsto_add_atTop_iff_nat N).mp hshift
