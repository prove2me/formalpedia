-- Prove2me | Definitions.Def_ErdosProblems_Erdos1049_ActualSourceResiduesR14
-- name    : ErdosProblems_Erdos1049_ActualSourceResiduesR14
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T17:48:29.99255+00:00
-- url     : https://prove2.me/theorems/607d08d4-f4e1-4978-aea3-f36c31c063b4
-- title:
--   Partial-fraction coefficients of the literal 2004 rational kernel
-- statement:
--   A finite simple-pole interpolation computes coefficients in the 1/(1−b_s z) basis for the literal 2004 rational kernel, whose denominator has 13n+1 factors; these coefficients match the existing A summands. The submitted module contains the source declarations sourcePoleParameter, sourceKernelNumerator, sourceKernelDenominator, sourceRationalKernel, sourceKernelNumerator_degree, among others. Source topic: Partial-fraction coefficients of the literal 2004 rational kernel.
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos1049/ActualSourceResiduesR14.lean#L20-L171
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
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
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

/-!
# Residues of the literal 2004 rational kernel

Proves the partial-fraction residues of the 2004 rational kernel.

The denominator has 13*n+1 factors, as in the corrected analytic source.
Its residues are proved to be the existing integral A_s evaluated at 1/q,
with the exact pole-power factor. No abstract A/B pair is substituted.
-/
namespace ErdosProblems.Erdos1049.PaperR14
set_option maxHeartbeats 1000000
open Polynomial Finset
open PaperR10 PaperR11 PaperR12
open scoped BigOperators

noncomputable def sourcePoleParameter (q : ℝ) (n s : ℕ) : ℝ :=
  q ^ (14 * n + 1 + s)

noncomputable def sourceKernelNumerator (q : ℝ) (n : ℕ) : ℝ[X] :=
  C (qPochhammer q q (13 * n) / qPochhammer q q (12 * n)) *
    poleProduct (fun i : ℕ => q ^ (i + 1)) (range (12 * n))

noncomputable def sourceKernelDenominator (q : ℝ) (n : ℕ) : ℝ[X] :=
  poleProduct (sourcePoleParameter q n) (range (13 * n + 1))

noncomputable def sourceRationalKernel (q : ℝ) (n : ℕ) (z : ℝ) : ℝ :=
  (sourceKernelNumerator q n).eval z / (sourceKernelDenominator q n).eval z















end ErdosProblems.Erdos1049.PaperR14


