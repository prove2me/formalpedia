-- Prove2me | Definitions.Def_ErdosProblems_Erdos1049_ActualSourceAnalyticIdentityR14
-- name    : ErdosProblems_Erdos1049_ActualSourceAnalyticIdentityR14
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T17:49:19.971435+00:00
-- url     : https://prove2.me/theorems/797f5298-ad3c-4ccb-bd3c-903c09c3246e
-- title:
--   The actual analytic identity A_n F - B_n = H_n
-- statement:
--   Actual coefficients in the 1/(1−b_s z) partial-fraction basis identify A·F−B with the source pole series. The initial 12n terms vanish and the remaining absolutely convergent series shifts to H. The submitted module contains the source declarations power_quotient_eq, source_shifted_pole, source_shifted_residue_power, sourceExtendedKernelTerm, sourcePoleSeriesTerm_eq_extended, among others. Source topic: The actual analytic identity A_n F - B_n = H_n.
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos1049/ActualSourceAnalyticIdentityR14.lean#L20-L162
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
# The actual analytic identity A_n F - B_n = H_n

Proves A_n F - B_n = H_n for the literal source at every 0 < q < 1.

The proof uses the actual residues, proves that the first 12*n terms vanish,
and shifts the absolutely convergent series. The last Pochhammer has length
13*n+1, including n=0. No source identity or summability assertion is assumed.
-/
namespace ErdosProblems.Erdos1049.PaperR14
set_option maxHeartbeats 1000000
open Polynomial Finset
open PaperR10 PaperR11 PaperR12
open scoped BigOperators







noncomputable def sourceExtendedKernelTerm (q : ℝ) (n t : ℕ) : ℝ :=
  (q ^ ((14 * n + 1) * t) / q ^ ((14 * n + 1) * (12 * n))) *
    sourceRationalKernel q n (q ^ t / q ^ (12 * n))

















end ErdosProblems.Erdos1049.PaperR14


