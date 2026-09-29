-- Prove2me | Theorems.Thm_ErdosProblems_Erdos1049_PaperR10_rate_quotient_eq_contour
-- name    : ErdosProblems.Erdos1049.PaperR10.rate_quotient_eq_contour
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T18:15:22.466204+00:00
-- url     : https://prove2.me/theorems/864cac7d-5960-4653-badb-60f4e7e3194e
-- title:
--   Rate quotient eq contour
-- statement:
--   For natural a,b with log a>0 and C₀ log a−C₁ log b>0, the expression 1+(C₁−C₀)log a/(C₀ log a−C₁ log b) equals rationalBaseMeasureBound(a,b).
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos1049/MeasureConstantsR10.lean#L226-L242
--   Paper exposition and prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/1049/erdos-1049-rational-base-lambert.tex#L1252-L1257
--   Correspondence: Erdős #1049 formal source; the rational-base Lambert-series method follows Zudilin, without a novelty or universal rational-base claim.

import Definitions.Def_ErdosProblems_Erdos1049_BezoutPluckerJets
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinHeightRegion
import Definitions.Def_ErdosProblems_Erdos1049_RationalBaseContour
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinConeArithmetic
import Definitions.Def_ErdosProblems_Erdos1049_PaperLinearFormsR7
import Definitions.Def_ErdosProblems_Erdos1049_PaperAsymptoticsR9
import Definitions.Def_ErdosProblems_Erdos1049_QuadraticMeasureR10
import Definitions.Def_ErdosProblems_Erdos1049_MeasureConstantsR10
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
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open ErdosProblems.Erdos1049.PaperR10

theorem ErdosProblems.Erdos1049.PaperR10.rate_quotient_eq_contour (a b : ℕ)
    (ha : 0 < Real.log (a : ℝ))
    (hτ : 0 < zudilinC0 * Real.log a - zudilinC1 * Real.log b) :
    1 + ((zudilinC1 - zudilinC0) * Real.log a) /
        (zudilinC0 * Real.log a - zudilinC1 * Real.log b) =
      rationalBaseMeasureBound a b := by sorry
