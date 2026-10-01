-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperCompleteR21.rpow_lt_iff_log_ratio
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-30T22:09:43.20199+00:00
-- url     : https://prove2.me/submissions/fcf831a3-64c0-4229-b8e9-b85c5fd2aaea

import Definitions.Def_ErdosProblems_Erdos1049_BezoutPluckerJets
import Definitions.Def_ErdosProblems_Erdos1049_QBinomialUnitIdentity
import Definitions.Def_ErdosProblems_Erdos1049_FiniteResidueInterpolationR14
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinHeightRegion
import Definitions.Def_ErdosProblems_Erdos1049_RationalBaseContour
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinConeArithmetic
import Definitions.Def_ErdosProblems_Erdos1049_PaperLinearFormsR7
import Definitions.Def_ErdosProblems_Erdos1049_PaperOmegaIndicatorR7
import Definitions.Def_ErdosProblems_Erdos1049_QProductBoundsR10
import Definitions.Def_ErdosProblems_Erdos1049_SourcePolynomialR11
import Definitions.Def_ErdosProblems_Erdos1049_SourceBClearingR12
import Definitions.Def_ErdosProblems_Erdos1049_LambertSourceSummationR14
import Definitions.Def_ErdosProblems_Erdos1049_ReciprocalPochhammerR14
import Definitions.Def_ErdosProblems_Erdos1049_ActualSourceResiduesR14
import Definitions.Def_ErdosProblems_Erdos1049_PaperAsymptoticsR9
import Definitions.Def_ErdosProblems_Erdos1049_SourcePositiveHBoundsR10
import Definitions.Def_ErdosProblems_Erdos1049_ActualSourceAnalyticIdentityR14
import Definitions.Def_ErdosProblems_Erdos1049_GaussianDegreeR12
import Definitions.Def_ErdosProblems_Erdos1049_PaperShortCapR9
import Definitions.Def_ErdosProblems_Erdos1049_SourceFiniteTransformR12
import Definitions.Def_ErdosProblems_Erdos1049_SourceHomogeneousR12
import Definitions.Def_ErdosProblems_Erdos1049_RootUnityLocalCancellationR13
import Definitions.Def_ErdosProblems_Erdos1049_SourceBMonomialR12
import Definitions.Def_ErdosProblems_Erdos1049_SourceBTopDegreeR13
import Definitions.Def_ErdosProblems_Erdos1049_SourceRootCarriesR13
import Definitions.Def_ErdosProblems_Erdos1049_SourceRootBlocksR13
import Definitions.Def_ErdosProblems_Erdos1049_SourceOmegaCancellationR13
import Definitions.Def_ErdosProblems_Erdos1049_ActualAGrowthR14
import Definitions.Def_ErdosProblems_Erdos1049_G02ArithmeticR16
import Definitions.Def_ErdosProblems_Erdos1049_SourceHeightRateR14
import Definitions.Def_ErdosProblems_Erdos1049_WeightedFloorBlocksR12
import Definitions.Def_ErdosProblems_Erdos1049_G02WeightedBlocksR16
import Definitions.Def_ErdosProblems_Erdos1049_G02CyclotomicR16
import Definitions.Def_ErdosProblems_Erdos1049_G02SourceRatesR16
import Definitions.Def_ErdosProblems_Erdos1049_QuadraticMeasureR10
import Definitions.Def_ErdosProblems_Erdos1049_IrrationalityExponentR11
import Definitions.Def_ErdosProblems_Erdos1049_MeasureConstantsR10
import Definitions.Def_ErdosProblems_Erdos1049_PaperR17_SourceConsumers
import Definitions.Def_ErdosProblems_Erdos1049_PaperCompleteR21_RationalBaseThreshold
import Lean.Elab.Tactic.Omega
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Module.Prod
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Coprime
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Order.LiminfLimsup
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Erdős #1049: the rational-base threshold in its paper form

Paper restatements of

* `res:rational-base-threshold` / `long1049:res:region` (the rational-base
  region, stated with the paper's hypothesis `b^μ < a` and with the paper's
  "equivalently" `b^μ < a ↔ log b / log a < θ*` proved, not assumed);
* `long1049:res:31over4` (the base `31/4`, its powers, and the two displayed
  chains `1/2 - 1/π² < log 4 / log 31 < 81/200 < θ*` and `4^μ < 31 < 4^{μ_BV}`
  with `μ_BV = 2π²/(π²-2)`);
* `cor:rational-base-measure` / `long1049:cor:rational-base-measure`
  (the irrationality measure uniform over powers).

Nothing here assumes an external theorem: the supplier comes from
`PaperR17.SourceConsumers`, which is itself proved in the tree.

The truncated decimal displays printed in those environments
(`θ* = 0.40568302138406054…`, `μ = 2.4649786835749750…`,
`log 4 / log 31 = 0.4036981731641997…`, `4^μ = 30.483515…`,
`4^{μ_BV} = 32.369642…`, `μ_BV = 2.508284761994…`,
`1/2 - 1/π² = 0.3986788163576622…`) are NOT proved here; only the bracketing
inequalities below are.
-/

namespace ErdosProblems.Erdos1049.PaperCompleteR21
open ErdosProblems.Erdos1049
open ErdosProblems.Erdos1049.PaperR7
open ErdosProblems.Erdos1049.PaperR10
open ErdosProblems.Erdos1049.PaperR11

/-! ## A real-power comparison used twice -/
end ErdosProblems.Erdos1049.PaperCompleteR21

open ErdosProblems.Erdos1049
open ErdosProblems.Erdos1049.PaperR7
open ErdosProblems.Erdos1049.PaperR10
open ErdosProblems.Erdos1049.PaperR11
open ErdosProblems in
open ErdosProblems.Erdos1049 in
open ErdosProblems.Erdos1049.PaperCompleteR21 in
theorem solution {x y c : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hlogy : 0 < Real.log y) (hc : 0 < c) :
    x ^ c < y ↔ Real.log x / Real.log y < 1 / c := by
  rw [div_lt_iff₀ hlogy, one_div, inv_mul_eq_div, lt_div_iff₀ hc]
  constructor
  · intro h
    have h0 : Real.exp (Real.log x * c) < Real.exp (Real.log y) := by
      rw [Real.exp_log hy]
      rwa [Real.rpow_def_of_pos hx] at h
    exact Real.exp_lt_exp.mp h0
  · intro h
    have h0 : Real.exp (Real.log x * c) < Real.exp (Real.log y) := Real.exp_lt_exp.mpr h
    rw [Real.exp_log hy] at h0
    rwa [Real.rpow_def_of_pos hx]
