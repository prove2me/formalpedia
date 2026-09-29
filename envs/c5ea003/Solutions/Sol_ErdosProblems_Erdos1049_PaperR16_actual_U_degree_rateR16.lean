-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperR16.actual_U_degree_rateR16
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:38:55.535612+00:00
-- url     : https://prove2.me/submissions/26a26f6a-d635-47b6-a1f2-c840d8ce5d3e

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
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR16_QuadRateR16_congr_eventually
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR12_sourceComplement_monic_degree
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR12_actual_U_degree
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR13_sourceK_gt_M
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR14_sourceK_quadratic_residual
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR16_QuadRateR16_add
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR16_QuadRateR16_sub
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR16_actual_complement_degree_rateR16
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR16_rate_of_eventual_linear_errorR16
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

namespace PaperR10
end PaperR10

namespace PaperR11
end PaperR11

namespace PaperR12
end PaperR12

namespace PaperR13
end PaperR13

namespace PaperR14
end PaperR14

namespace PaperR9
end PaperR9

/-!
# G02 literal source-rate assembly

Every endpoint below specialises the actual R11/R13 U,V and R9 remainder.
No totient, cyclotomic, degree, or remainder rate is a hypothesis of the
final source theorem. Proves exact quadratic rates of U, V, A and the remainder.
This is not a construction of a new common-width four-jet family.
-/

namespace ErdosProblems.Erdos1049.PaperR16
open Polynomial Finset Filter Asymptotics
open PaperR9 PaperR10 PaperR11 PaperR12 PaperR13 PaperR14
open scoped BigOperators Topology
set_option maxHeartbeats 3000000






lemma sourceM_rateR16 : QuadRateR16 (fun n => (sourceM n : ℝ)) 266 := by
  apply rate_of_eventual_linear_errorR16 _ 266 35 (by norm_num)
  exact Eventually.of_forall (fun n => by
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    have he : (sourceM n : ℝ)-266*sqScale n = 34*(n : ℝ)+1 := by
      simp only [sourceM, sqScale, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      ring
    rw [he, abs_of_nonneg (by positivity)]
    nlinarith)

lemma sourceK_rateR16 : QuadRateR16 (fun n => (sourceK n : ℝ)) sourceC1R16 := by
  apply rate_of_eventual_linear_errorR16 _ sourceC1R16 42 (by norm_num)
  exact Eventually.of_forall (fun n => by
    simpa only [sourceC1R16, sqScale] using sourceK_quadratic_residual n)

lemma actual_U_degree_identityR16 (n : ℕ) (hn : 1 ≤ n) :
    ((sourceU n).natDegree : ℝ) =
      (sourceK n : ℝ)-(sourceM n : ℝ)+complementDegreeR16 n := by
  have hk := (sourceK_gt_M n hn).le
  rw [actual_U_degree, Nat.cast_add, Nat.cast_sub hk]
  unfold complementDegreeR16
  rw [(sourceComplement_monic_degree n).2]
end ErdosProblems.Erdos1049.PaperR16

open Polynomial Finset Filter Asymptotics
open PaperR9 PaperR10 PaperR11 PaperR12 PaperR13 PaperR14
open scoped BigOperators Topology
set_option maxHeartbeats 3000000
open ErdosProblems in
open ErdosProblems.Erdos1049 in
open ErdosProblems.Erdos1049.PaperR16 in
open ErdosProblems.Erdos1049.PaperR10 in
open ErdosProblems.Erdos1049.PaperR11 in
open ErdosProblems.Erdos1049.PaperR12 in
open ErdosProblems.Erdos1049.PaperR13 in
open ErdosProblems.Erdos1049.PaperR14 in
open ErdosProblems.Erdos1049.PaperR9 in
theorem solution :
    QuadRateR16 (fun n => ((sourceU n).natDegree : ℝ)) sourceDeltaR16 := by
  have h := (sourceK_rateR16.sub sourceM_rateR16).add actual_complement_degree_rateR16
  have hc : sourceC1R16-266+sourceGammaR16=sourceDeltaR16 := by
    unfold sourceDeltaR16 sourceC0R16
    ring
  rw [hc] at h
  apply h.congr_eventually
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  exact (actual_U_degree_identityR16 n hn).symm
