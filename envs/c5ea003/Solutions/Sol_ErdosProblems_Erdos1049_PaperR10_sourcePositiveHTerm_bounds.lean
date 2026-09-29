-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperR10.sourcePositiveHTerm_bounds
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T21:59:05.875872+00:00
-- url     : https://prove2.me/submissions/5813f1b7-daa4-4c2f-846f-1d2f3965be7a

import Definitions.Def_ErdosProblems_Erdos1049_BezoutPluckerJets
import Definitions.Def_ErdosProblems_Erdos1049_QProductBoundsR10
import Definitions.Def_ErdosProblems_Erdos1049_PaperAsymptoticsR9
import Definitions.Def_ErdosProblems_Erdos1049_SourcePositiveHBoundsR10
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR10_qPochhammerInfinity_pos
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR10_quotient_of_unit_interval_bounds
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR10_shifted_qPochhammer_bounds
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
end ErdosProblems.Erdos1049.PaperR10

open Filter
open scoped BigOperators Topology
open ErdosProblems in
open ErdosProblems.Erdos1049 in
open ErdosProblems.Erdos1049.PaperR10 in
theorem solution {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (n t : ℕ) :
    q ^ ((14 * n + 1) * t) * (qPochhammerInfinity q q) ^ 2 ≤
        sourcePositiveHTerm q n t ∧
    sourcePositiveHTerm q n t ≤
        (qPochhammerInfinity q q)⁻¹ ^ 2 * (q ^ (14 * n + 1)) ^ t := by
  let P := qPochhammerInfinity q q
  have hP : 0 < P := qPochhammerInfinity_pos q q
  have h1 := shifted_qPochhammer_bounds hq0 hq1 (t + 1) (12 * n) (by omega)
  have h2 := shifted_qPochhammer_bounds hq0 hq1 1 (12 * n) (by omega)
  have h3 := shifted_qPochhammer_bounds hq0 hq1 1 (13 * n) (by omega)
  have h4 := shifted_qPochhammer_bounds hq0 hq1 (14 * n + 1 + t) (13 * n + 1) (by omega)
  simp only [pow_one] at h2 h3
  have hr1 := quotient_of_unit_interval_bounds hP h1 h2
  have hr2 := quotient_of_unit_interval_bounds hP h3 h4
  have hpow : 0 ≤ q ^ ((14 * n + 1) * t) := pow_nonneg hq0.le _
  have hlo := mul_le_mul hr1.1 hr2.1 hP.le (hP.le.trans hr1.1)
  have hup := mul_le_mul hr1.2 hr2.2 (hP.le.trans hr2.1) (inv_nonneg.mpr hP.le)
  constructor
  · have hh := mul_le_mul_of_nonneg_left hlo hpow
    simpa only [sourcePositiveHTerm, P, pow_two, mul_assoc] using hh
  · have hh := mul_le_mul_of_nonneg_left hup hpow
    calc
      sourcePositiveHTerm q n t ≤
          q ^ ((14 * n + 1) * t) * (P⁻¹ * P⁻¹) := by
        simpa only [sourcePositiveHTerm, P, mul_assoc] using hh
      _ = P⁻¹ ^ 2 * (q ^ (14 * n + 1)) ^ t := by
        rw [pow_mul, pow_two]
        ring
