-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperR10.sourcePositiveH_bounds
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T22:00:12.338361+00:00
-- url     : https://prove2.me/submissions/4372b361-bb78-4a2e-881a-1b355aa10d3b

import Definitions.Def_ErdosProblems_Erdos1049_BezoutPluckerJets
import Definitions.Def_ErdosProblems_Erdos1049_QProductBoundsR10
import Definitions.Def_ErdosProblems_Erdos1049_PaperAsymptoticsR9
import Definitions.Def_ErdosProblems_Erdos1049_SourcePositiveHBoundsR10
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR10_summable_nonneg_dominated
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR10_qpow_antitone
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR10_sourcePositiveHTerm_bounds
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Module.Prod
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# The actual positive 2004 source series in direction (14,12,14;27)

This module CONSTRUCTS the positive hypergeometric series,
proves its convergence, proves uniform two-sided bounds, and proves its exact
zero quadratic logarithmic rate. In particular none of those properties is
an added hypothesis.

The last denominator has length 13*n+1. Replacing it by 13*n would be the
historical off-by-one error identified in the supplied notes.

The identity with the cancelled integer polynomial linear form is not asserted
here: that algebraic/arithmetic source transport remains separately identified.
-/

namespace ErdosProblems.Erdos1049.PaperR10
open Filter
open scoped BigOperators Topology









theorem sourcePositiveHTerm_nonneg {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (n t : ℕ) : 0 ≤ sourcePositiveHTerm q n t :=
  (mul_nonneg (pow_nonneg hq0.le _) (sq_nonneg _)).trans
    (sourcePositiveHTerm_bounds hq0 hq1 n t).1

/-- Convergence is proved before any use of tsum comparison. -/
theorem summable_sourcePositiveHTerm {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (n : ℕ) : Summable (sourcePositiveHTerm q n) := by
  have hqn : q ^ (14 * n + 1) < 1 := by
    have h := qpow_antitone hq0.le hq1.le (by omega : 1 ≤ 14 * n + 1)
    have hqpow1 : q ^ 1 < 1 := by simpa only [pow_one] using hq1
    exact h.trans_lt hqpow1
  apply summable_nonneg_dominated (sourcePositiveHTerm_nonneg hq0 hq1 n)
    (fun t => (sourcePositiveHTerm_bounds hq0 hq1 n t).2)
  exact (summable_geometric_of_lt_one (pow_nonneg hq0.le _) hqn).mul_left _
end ErdosProblems.Erdos1049.PaperR10

open Filter
open scoped BigOperators Topology
open ErdosProblems in
open ErdosProblems.Erdos1049 in
open ErdosProblems.Erdos1049.PaperR10 in
theorem solution {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (n : ℕ) :
    (qPochhammerInfinity q q) ^ 2 ≤ sourcePositiveH q n ∧
      sourcePositiveH q n ≤ (qPochhammerInfinity q q)⁻¹ ^ 2 /
        (1 - q ^ (14 * n + 1)) := by
  have hs := summable_sourcePositiveHTerm hq0 hq1 n
  have hqn : q ^ (14 * n + 1) < 1 := by
    have h := qpow_antitone hq0.le hq1.le (by omega : 1 ≤ 14 * n + 1)
    have hqpow1 : q ^ 1 < 1 := by simpa only [pow_one] using hq1
    exact h.trans_lt hqpow1
  constructor
  · have ht := (sourcePositiveHTerm_bounds hq0 hq1 n 0).1
    simp only [Nat.mul_zero, pow_zero, one_mul] at ht
    exact ht.trans (hs.le_tsum 0 (fun k _ => sourcePositiveHTerm_nonneg hq0 hq1 n k))
  · have hg := (hasSum_geometric_of_lt_one (pow_nonneg hq0.le _) hqn).mul_left
      ((qPochhammerInfinity q q)⁻¹ ^ 2)
    calc
      sourcePositiveH q n ≤ ∑' t : ℕ,
          (qPochhammerInfinity q q)⁻¹ ^ 2 * (q ^ (14 * n + 1)) ^ t :=
        Summable.tsum_le_tsum (fun t => (sourcePositiveHTerm_bounds hq0 hq1 n t).2)
          hs hg.summable
      _ = _ := by simpa only [div_eq_mul_inv] using hg.tsum_eq
