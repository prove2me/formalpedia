-- Prove2me | Definitions.Def_ErdosProblems_Erdos1049_QuadraticMeasureR10
-- name    : ErdosProblems_Erdos1049_QuadraticMeasureR10
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T17:46:22.548266+00:00
-- url     : https://prove2.me/theorems/dfdca881-1c0a-4b42-960a-155e77f23b79
-- title:
--   A complete quadratic-mesh irrationality-measure consumer
-- statement:
--   Quadratic linear forms separate all integer numerators from sufficiently large positive denominators, giving a uniform approximation-exponent upper bound. The submitted module contains the source declarations ApproximationExponentUpper, separation_of_exponential_envelope, exists_quadratic_crossing, approximationExponentUpper_of_quadratic_forms, irrational_and_measure_of_quadratic_forms. Source topic: A complete quadratic-mesh irrationality-measure consumer.
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos1049/QuadraticMeasureR10.lean#L18-L198
--   Paper exposition and prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/1049/erdos-1049-rational-base-lambert.tex#L1252-L1257
--   Correspondence: Erdős #1049 formal source; Zudilin is credited for the relevant rational-base Lambert-series method, without a novelty or all-rational-base claim.

import Definitions.Def_ErdosProblems_Erdos1049_BezoutPluckerJets
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinHeightRegion
import Definitions.Def_ErdosProblems_Erdos1049_RationalBaseContour
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinConeArithmetic
import Definitions.Def_ErdosProblems_Erdos1049_PaperLinearFormsR7
import Definitions.Def_ErdosProblems_Erdos1049_PaperAsymptoticsR9
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
# A complete quadratic-mesh irrationality-measure consumer

The conclusion is uniform over all integer numerators
and all sufficiently large positive denominators. No independence assumption
on successive coefficient pairs is used. The actual 2004 source construction
is NOT asserted by this module.
-/
namespace ErdosProblems.Erdos1049.PaperR10
open Filter
open scoped Topology
open PaperR9

/-- The eventual approximation formulation of an upper irrationality exponent.
It uses every integer numerator, so in particular covers reduced fractions. -/
def ApproximationExponentUpper (ξ μ : ℝ) : Prop :=
  ∀ ν : ℝ, μ < ν → ∃ q₀ : ℕ, 0 < q₀ ∧
    ∀ q : ℕ, q₀ ≤ q → ∀ p : ℤ,
      (q : ℝ) ^ (-ν) ≤ |ξ - (p : ℝ) / (q : ℝ)|









end ErdosProblems.Erdos1049.PaperR10


