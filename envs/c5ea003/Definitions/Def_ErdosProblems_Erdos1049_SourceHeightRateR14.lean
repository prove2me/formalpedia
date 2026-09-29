-- Prove2me | Definitions.Def_ErdosProblems_Erdos1049_SourceHeightRateR14
-- name    : ErdosProblems_Erdos1049_SourceHeightRateR14
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T17:57:10.253295+00:00
-- url     : https://prove2.me/theorems/f93ead6b-4221-4608-8a33-d86eb003e6a1
-- title:
--   Subquadratic coefficient heights of the actual cancelled source pair
-- statement:
--   All-index coefficient bounds for the actual cancelled U,V pair imply subquadratic logarithmic heights through circle estimates and a degree-plus-one transport. The submitted module contains the source declarations sourceRadius, sourceLogScale, sourceCoefficientEnvelope, sourceRadius_gt_one, sourceLogScale_ge_one, among others. Source topic: Subquadratic coefficient heights of the actual cancelled source pair.
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos1049/SourceHeightRateR14.lean#L21-L397
--   Paper exposition and prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/1049/erdos-1049-rational-base-lambert.tex#L1252-L1257
--   Correspondence: Erdős #1049 formal source; Zudilin is credited for the relevant rational-base Lambert-series method, without a novelty or all-rational-base claim.

import Definitions.Def_ErdosProblems_Erdos1049_BezoutPluckerJets
import Definitions.Def_ErdosProblems_Erdos1049_QBinomialUnitIdentity
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinConeArithmetic
import Definitions.Def_ErdosProblems_Erdos1049_PaperOmegaIndicatorR7
import Definitions.Def_ErdosProblems_Erdos1049_SourcePolynomialR11
import Definitions.Def_ErdosProblems_Erdos1049_SourceBClearingR12
import Definitions.Def_ErdosProblems_Erdos1049_PaperAsymptoticsR9
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
import Lean.Elab.Tactic.Omega
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Module.Prod
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Coprime
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.LiminfLimsup
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Subquadratic coefficient heights of the actual cancelled source pair

Proves the cancelled pair's coefficient heights have zero quadratic log rate.

This file uses the actual `sourceU` and `sourceV`, the all-index coefficient
bound from R13, and the unchanged maximum/l1 height definitions of the papers.
The analytic limit and the degree+1 transport are proved here, not assumed.
The intentionally conservative numerical envelope is 5000*n*(1+log(n+2))^2.
-/
namespace ErdosProblems.Erdos1049.PaperR14
set_option maxHeartbeats 1000000
open Polynomial Finset Filter Asymptotics
open PaperR11 PaperR12 PaperR13
open scoped BigOperators Topology


noncomputable def sourceLogScale (n : ℕ) : ℝ := 1 + Real.log ((n : ℝ) + 2)






















































end ErdosProblems.Erdos1049.PaperR14


