-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperR10.quotient_of_unit_interval_bounds
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T21:52:57.447026+00:00
-- url     : https://prove2.me/submissions/eb44aa1a-1b13-4ac0-a815-0b648eb0df8a

import Definitions.Def_ErdosProblems_Erdos1049_BezoutPluckerJets
import Definitions.Def_ErdosProblems_Erdos1049_QProductBoundsR10
import Definitions.Def_ErdosProblems_Erdos1049_PaperAsymptoticsR9
import Definitions.Def_ErdosProblems_Erdos1049_SourcePositiveHBoundsR10
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
theorem solution {P A B : ℝ} (hP : 0 < P)
    (hA : P ≤ A ∧ A ≤ 1) (hB : P ≤ B ∧ B ≤ 1) :
    P ≤ A / B ∧ A / B ≤ P⁻¹ := by
  have hBpos : 0 < B := hP.trans_le hB.1
  constructor
  · apply (le_div_iff₀ hBpos).mpr
    calc
      P * B ≤ P * 1 := mul_le_mul_of_nonneg_left hB.2 hP.le
      _ = P := by ring
      _ ≤ A := hA.1
  · calc
      A / B ≤ 1 / B := div_le_div_of_nonneg_right hA.2 hBpos.le
      _ ≤ 1 / P := one_div_le_one_div_of_le hP hB.1
      _ = _ := one_div P
