-- Prove2me | solution 1 for ReweightedNPMLE.log_one_add_secondOrder_isLittleO
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T04:01:23.372808+00:00
-- url     : https://prove2.me/submissions/e735f9cf-d8e5-4831-b711-09cd390f91d8

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Order.Filter.Finite
import Mathlib.Tactic
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_FiniteOptimizerFiber
import Definitions.Def_ReweightedNPMLE_FittedContact
import Definitions.Def_ReweightedNPMLE_FittedEnvelope
import Definitions.Def_ReweightedNPMLE_FittedHessian
import Definitions.Def_ReweightedNPMLE_FittedRegularity
import Definitions.Def_ReweightedNPMLE_Weights
import Theorems.Thm_ReweightedNPMLE_tendsto_log_one_add_sub_linear_div_sq

/-!
# Hessian structure of the fitted likelihood value

This file turns the envelope identity into the analytic Hessian facts used by
the paper.  The derivative of the fitted log-vector induces the second
derivative of the optimized value.  Mathlib's second-derivative symmetry
theorem makes its matrix Hermitian, while monotonicity of fitted logs makes
its quadratic form nonnegative.  Thus, at every differentiability point, the
matrix representing the fitted-log derivative is positive semidefinite.
-/

open Set Filter Asymptotics
open Matrix
open scoped BigOperators Topology

open ReweightedNPMLE
open ReweightedNPMLE in
/-- `log (1+tq) = tq - t²q²/2 + o(t²)` on the positive side. -/
theorem solution (q : ℝ) :
    (fun t : ℝ ↦ Real.log (1 + t * q) - t * q +
        (t ^ 2 / 2) * q ^ 2) =o[nhdsWithin 0 (Ioi 0)] (fun t : ℝ ↦ t ^ 2) := by
  rw [isLittleO_iff_tendsto]
  · have hbase := (tendsto_log_one_add_sub_linear_div_sq q).mono_left
        (nhdsWithin_mono 0 (show Ioi (0 : ℝ) ⊆ {0}ᶜ by
          intro t ht
          simp only [mem_compl_iff, mem_singleton_iff]
          exact ne_of_gt ht))
    have hadd : Tendsto
        (fun t : ℝ ↦ (Real.log (1 + t * q) - t * q) / t ^ 2 + q ^ 2 / 2)
        (nhdsWithin 0 (Ioi 0)) (nhds (-(q ^ 2) / 2 + q ^ 2 / 2)) :=
      hbase.add tendsto_const_nhds
    have hzero : -(q ^ 2) / 2 + q ^ 2 / 2 = 0 := by ring
    rw [hzero] at hadd
    apply hadd.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : t ≠ 0 := ne_of_gt ht
    field_simp [ht0]
  · intro t ht
    have ht0 : t = 0 := sq_eq_zero_iff.mp ht
    subst t
    simp
