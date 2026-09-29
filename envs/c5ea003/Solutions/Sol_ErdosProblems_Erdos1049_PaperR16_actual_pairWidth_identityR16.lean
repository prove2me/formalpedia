-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperR16.actual_pairWidth_identityR16
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T21:48:52.057634+00:00
-- url     : https://prove2.me/submissions/9a033214-c7e0-47d5-9a73-2d3e3ebae151

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
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR13_actual_V_quotient_degree
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
theorem solution (n : ℕ) (hn : 1 ≤ n) :
    pairWidth sourceU sourceV n = (sourceU n).natDegree := by
  unfold pairWidth
  rw [actual_V_quotient_degree n hn]
  exact max_eq_left (Nat.sub_le _ _)
