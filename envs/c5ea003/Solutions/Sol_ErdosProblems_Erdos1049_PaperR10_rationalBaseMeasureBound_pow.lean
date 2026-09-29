-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperR10.rationalBaseMeasureBound_pow
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T18:12:56.359855+00:00
-- url     : https://prove2.me/submissions/475dddee-eff1-4a2c-b60e-f24f7f1a753b

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

namespace ErdosProblems.Erdos1049.PaperR10
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
end ErdosProblems.Erdos1049.PaperR10

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
open ErdosProblems in
open ErdosProblems.Erdos1049 in
open ErdosProblems.Erdos1049.PaperR10 in
theorem solution (a b r : ℕ) (hr : 0 < r) :
    rationalBaseMeasureBound (a ^ r) (b ^ r) = rationalBaseMeasureBound a b := by
  unfold rationalBaseMeasureBound
  rw [Nat.cast_pow, Nat.cast_pow, Real.log_pow, Real.log_pow]
  rw [mul_div_mul_left _ _ (by exact_mod_cast hr.ne')]
