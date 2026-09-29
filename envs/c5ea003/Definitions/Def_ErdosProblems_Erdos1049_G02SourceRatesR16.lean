-- Prove2me | Definitions.Def_ErdosProblems_Erdos1049_G02SourceRatesR16
-- name    : ErdosProblems_Erdos1049_G02SourceRatesR16
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T18:00:46.262808+00:00
-- url     : https://prove2.me/theorems/d9de79ed-1698-47f3-a123-4735577cb2e1
-- title:
--   G02 literal source-rate assembly
-- statement:
--   The literal U,V,A and remainder identities combine the arithmetic, cyclotomic, degree, and positivity results into exact quadratic source rates. The submitted module contains the source declarations sourceUEvalR16, sourceVEvalR16, sourceAEvalR16, sourceRemainderR16, sourceM_rateR16, among others. Source topic: G02 literal source-rate assembly.
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos1049/G02SourceRatesR16.lean#L21-L293
--   Paper exposition and prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/1049/erdos-1049-rational-base-lambert.tex#L1252-L1257
--   Correspondence: Erdős #1049 formal source; Zudilin is credited for the relevant rational-base Lambert-series method, without a novelty or all-rational-base claim.

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

noncomputable def sourceUEvalR16 (p : ℝ) (n : ℕ) : ℝ :=
  (sourceU n).eval₂ (Int.castRingHom ℝ) p

noncomputable def sourceAEvalR16 (p : ℝ) (n : ℕ) : ℝ :=
  (sourceA n).eval₂ (Int.castRingHom ℝ) p
noncomputable def sourceRemainderR16 (p : ℝ) (n : ℕ) : ℝ :=
  polynomialRemainder sourceU sourceV PaperR7.paperLambert p n



















































end ErdosProblems.Erdos1049.PaperR16


