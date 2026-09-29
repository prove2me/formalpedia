-- Prove2me | Theorems.Thm_ErdosProblems_Erdos1049_PaperR14_sourceLogScale_ge_one
-- name    : ErdosProblems.Erdos1049.PaperR14.sourceLogScale_ge_one
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T18:43:21.636985+00:00
-- url     : https://prove2.me/theorems/12a3be9b-efd1-4337-900c-ffa5dc7417f4
-- title:
--   Source log scale ge one
-- statement:
--   The source logarithmic scale 1+log(n+2) is at least one for every natural n.
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos1049/SourceHeightRateR14.lean#L31-L35
--   Paper exposition and prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/1049/erdos-1049-rational-base-lambert.tex#L1252-L1257
--   Correspondence: Erdős #1049 formal source; the rational-base Lambert-series method follows Zudilin, without a novelty or universal rational-base claim.

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
import Definitions.Def_ErdosProblems_Erdos1049_SourceHeightRateR14
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

namespace PaperR11
end PaperR11

namespace PaperR12
end PaperR12

namespace PaperR13
end PaperR13

/-!
# Subquadratic coefficient heights of the actual cancelled source pair

Proves the cancelled pair's coefficient heights have zero quadratic log rate.

This file uses the actual `sourceU` and `sourceV`, the all-index coefficient
bound from R13, and the unchanged maximum/l1 height definitions of the papers.
The analytic limit and the degree+1 transport are proved here, not assumed.
The intentionally conservative numerical envelope is 5000*n*(1+log(n+2))^2.
-/
set_option maxHeartbeats 1000000
open Polynomial Finset Filter Asymptotics
open PaperR11 PaperR12 PaperR13
open scoped BigOperators Topology

open ErdosProblems.Erdos1049.PaperR14

open ErdosProblems.Erdos1049.PaperR11
open ErdosProblems.Erdos1049.PaperR12
open ErdosProblems.Erdos1049.PaperR13

theorem ErdosProblems.Erdos1049.PaperR14.sourceLogScale_ge_one (n : ℕ) : 1 ≤ sourceLogScale n := by sorry
