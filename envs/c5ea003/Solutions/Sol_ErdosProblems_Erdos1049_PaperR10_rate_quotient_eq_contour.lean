-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperR10.rate_quotient_eq_contour
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T18:15:33.186901+00:00
-- url     : https://prove2.me/submissions/a0fb0fd4-e092-4ad2-8c3f-75c0b013e4a2

import Definitions.Def_ErdosProblems_Erdos1049_BezoutPluckerJets
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinHeightRegion
import Definitions.Def_ErdosProblems_Erdos1049_RationalBaseContour
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinConeArithmetic
import Definitions.Def_ErdosProblems_Erdos1049_PaperLinearFormsR7
import Definitions.Def_ErdosProblems_Erdos1049_PaperAsymptoticsR9
import Definitions.Def_ErdosProblems_Erdos1049_QuadraticMeasureR10
import Definitions.Def_ErdosProblems_Erdos1049_MeasureConstantsR10
import Theorems.Thm_ErdosProblems_Erdos1049_zudilinC1_pos
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
end ErdosProblems.Erdos1049.PaperR10

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
open ErdosProblems in
open ErdosProblems.Erdos1049 in
open ErdosProblems.Erdos1049.PaperR10 in
theorem solution (a b : ℕ)
    (ha : 0 < Real.log (a : ℝ))
    (hτ : 0 < zudilinC0 * Real.log a - zudilinC1 * Real.log b) :
    1 + ((zudilinC1 - zudilinC0) * Real.log a) /
        (zudilinC0 * Real.log a - zudilinC1 * Real.log b) =
      rationalBaseMeasureBound a b := by
  unfold rationalBaseMeasureBound zudilinContour
  have hC1 := zudilinC1_pos.ne'
  have hden : zudilinC0 / zudilinC1 - Real.log b / Real.log a ≠ 0 := by
    intro h
    have hh : zudilinC0 * Real.log a - zudilinC1 * Real.log b = 0 := by
      field_simp [hC1, ha.ne'] at h
      nlinarith
    exact hτ.ne' hh
  field_simp [hC1, ha.ne', hτ.ne', hden]
  <;> ring
