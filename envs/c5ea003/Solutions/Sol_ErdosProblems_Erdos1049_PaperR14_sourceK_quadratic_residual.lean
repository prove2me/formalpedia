-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperR14.sourceK_quadratic_residual
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T18:25:34.238763+00:00
-- url     : https://prove2.me/submissions/19ddf884-9344-439b-bed0-941e6dc29069

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
import Lean.Elab.Tactic.Omega
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Module.Prod
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Coprime
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.NumberTheory.ZetaValues
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

/-!
# Fixed-base growth of the actual alternating A polynomial

Proves two-sided fixed-base bounds and the quadratic log rate of A_n(p).

Gaussian reciprocity is proved from finite factorial identities. Every earlier
summand loses at least n powers against the last one. The resulting tail is
bounded by a constant times n*q^n, which tends to zero. Thus possible alternating
cancellation is controlled before logarithms or a quadratic rate are asserted.
-/

namespace ErdosProblems.Erdos1049.PaperR14
set_option maxHeartbeats 1000000
open Polynomial Finset Filter Asymptotics
open PaperR10 PaperR11 PaperR12
open scoped BigOperators Topology
end ErdosProblems.Erdos1049.PaperR14

set_option maxHeartbeats 1000000
open Polynomial Finset Filter Asymptotics
open PaperR10 PaperR11 PaperR12
open scoped BigOperators Topology
open ErdosProblems in
open ErdosProblems.Erdos1049 in
open ErdosProblems.Erdos1049.PaperR14 in
open ErdosProblems.Erdos1049.PaperR10 in
open ErdosProblems.Erdos1049.PaperR11 in
open ErdosProblems.Erdos1049.PaperR12 in
theorem solution (n : ℕ) :
    |(sourceK n : ℝ) - (1091 / 2 : ℝ) * (n : ℝ) ^ 2| ≤ 42 * (2 * (n : ℝ) + 1) := by
  let A := 1091 * n ^ 2 + 81 * n + 2
  have hm := Nat.mod_lt A (by norm_num : 0 < 2)
  have he := Nat.mod_add_div A 2
  have hlow : 2 * sourceK n ≤ A := by dsimp [sourceK, A]; omega
  have hupp : A < 2 * sourceK n + 2 := by dsimp [sourceK, A] at *; omega
  have hlow' : (2 : ℝ) * sourceK n ≤ 1091 * (n : ℝ) ^ 2 + 81 * n + 2 := by exact_mod_cast hlow
  have hupp' : 1091 * (n : ℝ) ^ 2 + 81 * n + 2 < (2 : ℝ) * sourceK n + 2 := by exact_mod_cast hupp
  rw [abs_le]
  constructor <;> nlinarith [Nat.cast_nonneg (α := ℝ) n]
