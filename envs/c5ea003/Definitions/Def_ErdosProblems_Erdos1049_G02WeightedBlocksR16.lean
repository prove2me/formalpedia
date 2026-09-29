-- Prove2me | Definitions.Def_ErdosProblems_Erdos1049_G02WeightedBlocksR16
-- name    : ErdosProblems_Erdos1049_G02WeightedBlocksR16
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T17:58:10.736797+00:00
-- url     : https://prove2.me/theorems/19b0821c-570f-44f5-9396-4357c67e4389
-- title:
--   Literal thirteen-block supplier: the complement degree has quadratic rate
-- statement:
--   The thirteen literal reciprocal blocks express the weighted complement degree, and quantitative totient-prefix errors vanish after quadratic rescaling. The submitted module contains the source declarations QuadRateR16, trigammaSeriesR16, blockKernelR16, sourceJR16, sourceJPrefixR16, among others. Source topic: Literal thirteen-block supplier: the complement degree has quadratic rate.
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos1049/G02WeightedBlocksR16.lean#L13-L620
--   Paper exposition and prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/1049/erdos-1049-rational-base-lambert.tex#L1252-L1257
--   Correspondence: Erdős #1049 formal source; Zudilin is credited for the relevant rational-base Lambert-series method, without a novelty or all-rational-base claim.

import Definitions.Def_ErdosProblems_Erdos1049_BezoutPluckerJets
import Definitions.Def_ErdosProblems_Erdos1049_QBinomialUnitIdentity
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinConeArithmetic
import Definitions.Def_ErdosProblems_Erdos1049_PaperOmegaIndicatorR7
import Definitions.Def_ErdosProblems_Erdos1049_QProductBoundsR10
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
import Definitions.Def_ErdosProblems_Erdos1049_G02ArithmeticR16
import Definitions.Def_ErdosProblems_Erdos1049_SourceHeightRateR14
import Definitions.Def_ErdosProblems_Erdos1049_WeightedFloorBlocksR12
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
import Mathlib.Analysis.SpecificLimits.Basic
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
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-! Literal thirteen-block supplier: the complement degree has quadratic rate. -/
namespace ErdosProblems.Erdos1049.PaperR16
open Finset Filter Asymptotics
open PaperR11 PaperR12
open scoped BigOperators Topology
set_option maxHeartbeats 4000000

/-- Additive quadratic rate. This is deliberately not a logarithmic rate. -/
def QuadRateR16 (f : ℕ → ℝ) (a : ℝ) : Prop :=
  (fun n => f n - a * PaperR9.sqScale n) =o[atTop] PaperR9.sqScale

noncomputable def trigammaSeriesR16 (u : ℝ) : ℝ :=
  ∑' k : ℕ, 1 / ((k : ℝ) + u)^2
noncomputable def blockKernelR16 (u v : ℝ) (k : ℕ) : ℝ :=
  1 / ((k : ℝ) + u)^2 - 1 / ((k : ℝ) + v)^2
noncomputable def sourceJR16 : ℝ :=
  ∑ uv ∈ sourceIntervals,
    (trigammaSeriesR16 (uv.1 : ℝ) - trigammaSeriesR16 (uv.2 : ℝ))
noncomputable def sourceJPrefixR16 (N : ℕ) : ℝ :=
  ∑ uv ∈ sourceIntervals, ∑ k ∈ range N,
    blockKernelR16 (uv.1 : ℝ) (uv.2 : ℝ) k
noncomputable def complementDegreeR16 (n : ℕ) : ℝ :=
  ((sourceComplement n).natDegree : ℝ)
noncomputable def sourceGammaR16 : ℝ := totientConstantR16 * (225 - sourceJR16)
noncomputable def sourceC0R16 : ℝ := 266 - sourceGammaR16
noncomputable def sourceC1R16 : ℝ := 1091 / 2
noncomputable def sourceDeltaR16 : ℝ := sourceC1R16 - sourceC0R16







































































end ErdosProblems.Erdos1049.PaperR16


