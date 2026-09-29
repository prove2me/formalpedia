-- Prove2me | Definitions.Def_ErdosProblems_Erdos1049_MeasureConstantsR10
-- name    : ErdosProblems_Erdos1049_MeasureConstantsR10
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T17:47:05.368362+00:00
-- url     : https://prove2.me/theorems/2a42918d-3a44-4cc8-9115-8c241a6d3dfb
-- title:
--   Exact constants for the power-uniform 31/4 bound
-- statement:
--   Finite rational partial sums bound the exact trigamma constant and lead to explicit inequalities for the 31/4 power measure. The submitted module contains the source declarations zudilinJ_sixteen_lower, zudilinContour_gt_40568, thirtyoneFour_power_certificate_2217, thirtyoneFour_ratio_lt_895_2217, thirtyoneFour_power_certificate_8058, among others. Source topic: Exact constants for the power-uniform 31/4 bound.
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos1049/MeasureConstantsR10.lean#L15-L247
--   Paper exposition and prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/1049/erdos-1049-rational-base-lambert.tex#L1252-L1257
--   Correspondence: Erdős #1049 formal source; Zudilin is credited for the relevant rational-base Lambert-series method, without a novelty or all-rational-base claim.

import Definitions.Def_ErdosProblems_Erdos1049_BezoutPluckerJets
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinHeightRegion
import Definitions.Def_ErdosProblems_Erdos1049_RationalBaseContour
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinConeArithmetic
import Definitions.Def_ErdosProblems_Erdos1049_PaperLinearFormsR7
import Definitions.Def_ErdosProblems_Erdos1049_PaperAsymptoticsR9
import Definitions.Def_ErdosProblems_Erdos1049_QuadraticMeasureR10
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Module.Prod
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Pigeonhole
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
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Exact constants for the power-uniform 31/4 bound

Finite rational sums bound the actual infinite trigamma
constant from below. These are unconditional parameter theorems, not an
assertion that the analytic source-form supplier has been formalised.
-/
namespace ErdosProblems.Erdos1049.PaperR10
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000















/-- The quotient appearing in the paper; this definition makes no assertion
about the irrationality exponent of a Lambert value. -/
noncomputable def rationalBaseMeasureBound (a b : ℕ) : ℝ :=
  (1 - Real.log b / Real.log a) /
    (zudilinContour - Real.log b / Real.log a)

















end ErdosProblems.Erdos1049.PaperR10


