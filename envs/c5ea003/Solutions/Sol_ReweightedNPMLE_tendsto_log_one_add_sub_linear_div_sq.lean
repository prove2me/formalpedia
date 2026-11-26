-- Prove2me | solution 1 for ReweightedNPMLE.tendsto_log_one_add_sub_linear_div_sq
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:00:20.522498+00:00
-- url     : https://prove2.me/submissions/ece72348-9da4-49ff-9845-431b3ed63d45

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
/-- The scalar logarithm expansion used in the support-sensitivity argument. -/
theorem solution (q : ℝ) :
    Tendsto (fun t : ℝ ↦ (Real.log (1 + t * q) - t * q) / t ^ 2)
      (nhdsWithin 0 {0}ᶜ) (nhds (-(q ^ 2) / 2)) := by
  let f : ℝ → ℝ := fun t ↦ Real.log (1 + t * q) - t * q
  let f' : ℝ → ℝ := fun t ↦ q / (1 + t * q) - q
  let g : ℝ → ℝ := fun t ↦ t ^ 2
  let g' : ℝ → ℝ := fun t ↦ 2 * t
  have hden : ∀ᶠ t in nhds (0 : ℝ), 1 + t * q ≠ 0 := by
    have hc : ContinuousAt (fun t : ℝ ↦ 1 + t * q) 0 := by fun_prop
    simpa using hc.eventually_ne (y := (0 : ℝ)) (by norm_num)
  have hff' : ∀ᶠ t in nhdsWithin (0 : ℝ) {0}ᶜ, HasDerivAt f (f' t) t := by
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds hden] with t ht
    dsimp [f, f']
    convert (((hasDerivAt_id t).mul_const q).const_add 1).log ht |>.sub
      ((hasDerivAt_id t).mul_const q) using 1 <;> simp [id_eq]
  have hgg' : ∀ᶠ t in nhdsWithin (0 : ℝ) {0}ᶜ, HasDerivAt g (g' t) t := by
    filter_upwards [] with t
    dsimp [g, g']
    convert (hasDerivAt_id t).pow 2 using 1 <;> simp [id_eq]
  have hg' : ∀ᶠ t in nhdsWithin (0 : ℝ) {0}ᶜ, g' t ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact mul_ne_zero (by norm_num) ht
  have hfa : Tendsto f (nhdsWithin (0 : ℝ) {0}ᶜ) (nhds 0) := by
    have hc : ContinuousAt f 0 := by
      dsimp [f]
      exact (((hasDerivAt_id 0).mul_const q).const_add 1).log (by norm_num) |>.sub
        ((hasDerivAt_id 0).mul_const q) |>.continuousAt
    simpa [f] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hga : Tendsto g (nhdsWithin (0 : ℝ) {0}ᶜ) (nhds 0) := by
    have hc : ContinuousAt g 0 := by
      dsimp [g]
      fun_prop
    simpa [g] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hdiv : Tendsto (fun t ↦ f' t / g' t) (nhdsWithin (0 : ℝ) {0}ᶜ)
      (nhds (-(q ^ 2) / 2)) := by
    have hc : Tendsto (fun t : ℝ ↦ -(q ^ 2) / (2 * (1 + t * q)))
        (nhdsWithin 0 {0}ᶜ) (nhds (-(q ^ 2) / 2)) := by
      have hcont : ContinuousAt (fun t : ℝ ↦ -(q ^ 2) / (2 * (1 + t * q))) 0 := by
        fun_prop (disch := norm_num)
      convert hcont.tendsto.mono_left nhdsWithin_le_nhds using 1 <;> norm_num
    apply hc.congr'
    filter_upwards [self_mem_nhdsWithin,
      eventually_nhdsWithin_of_eventually_nhds hden] with t ht htden
    have ht0 : t ≠ 0 := by simpa using ht
    have htden' : 1 + q * t ≠ 0 := by simpa [mul_comm] using htden
    dsimp [f', g']
    field_simp [ht0, htden'] <;> ring
  exact HasDerivAt.lhopital_zero_nhdsNE hff' hgg' hg' hfa hga hdiv
