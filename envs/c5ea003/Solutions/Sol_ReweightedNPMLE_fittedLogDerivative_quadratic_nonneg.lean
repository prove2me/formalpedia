-- Prove2me | solution 1 for ReweightedNPMLE.fittedLogDerivative_quadratic_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:02:35.444808+00:00
-- url     : https://prove2.me/submissions/5305dcc4-d0f3-4acc-9a48-f5903de0e24c

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
import Theorems.Thm_ReweightedNPMLE_fittedLog_monotone

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
theorem solution {n : ℕ} [Nonempty (Fin n)]
    {C : Set (Fin n → ℝ)}
    (vhat : (Fin n → ℝ) → (Fin n → ℝ))
    (hmax : ∀ u, IsMaxOn C (weightedLogLikelihood u) (vhat u))
    {w : Fin n → ℝ} {J : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)}
    (hz : HasFDerivAt (fun u i ↦ Real.log (vhat u i)) J w)
    (h : Fin n → ℝ) :
    0 ≤ ∑ i, h i * J h i := by
  let z : (Fin n → ℝ) → (Fin n → ℝ) :=
    fun u i ↦ Real.log (vhat u i)
  have hmono : ∀ u,
      0 ≤ ∑ i, (u i - w i) * (z u i - z w i) := by
    intro u
    exact fittedLog_monotone vhat
      (s := Set.univ) (fun q _ ↦ hmax q) u (Set.mem_univ u) w (Set.mem_univ w)
  have haffine : HasDerivAt (fun t : ℝ ↦ w + t • h) h 0 := by
    simpa using (hasDerivAt_id (𝕜 := ℝ) (x := 0)).smul_const h |>.const_add w
  have hline : HasDerivAt (fun t : ℝ ↦ z (w + t • h)) (J h) 0 := by
    have hz0 : HasFDerivAt (fun u i ↦ Real.log (vhat u i)) J
        ((fun t : ℝ ↦ w + t • h) 0) := by simpa using hz
    have hcomp := hz0.comp_hasDerivAt 0 haffine
    convert hcomp using 1 <;> simp [z, Function.comp_def]
  have htendVec := hline.tendsto_slope_zero
  have htend : Tendsto
      (fun t : ℝ ↦ fittedLogLinearFunctional h
        (t⁻¹ • (z (w + (0 + t) • h) - z (w + 0 • h))))
      (𝓝[≠] 0) (𝓝 (fittedLogLinearFunctional h (J h))) := by
    have hcont : Tendsto (fittedLogLinearFunctional h) (𝓝 (J h))
        (𝓝 (fittedLogLinearFunctional h (J h))) :=
      (fittedLogLinearFunctional h).continuous.tendsto (J h)
    have hcomp := hcont.comp htendVec
    simpa [Function.comp_def] using hcomp
  have hnonneg : 0 ≤ fittedLogLinearFunctional h (J h) := by
    apply ge_of_tendsto htend
    filter_upwards [self_mem_nhdsWithin] with t ht
    have htne : t ≠ 0 := ht
    have hm := hmono (w + t • h)
    have hm' : 0 ≤ t * ∑ i, h i * (z (w + t • h) i - z w i) := by
      convert hm using 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have heq : fittedLogLinearFunctional h
        (t⁻¹ • (z (w + (0 + t) • h) - z (w + 0 • h))) =
        (t * ∑ i, h i * (z (w + t • h) i - z w i)) / t ^ 2 := by
      rw [fittedLogLinearFunctional_apply]
      simp only [zero_add, zero_smul, add_zero, Pi.smul_apply, Pi.sub_apply,
        smul_eq_mul]
      calc
        (∑ i, t⁻¹ * (z (w + t • h) i - z w i) * h i) =
            t⁻¹ * ∑ i, h i * (z (w + t • h) i - z w i) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = (t * ∑ i, h i * (z (w + t • h) i - z w i)) / t ^ 2 := by
          field_simp [htne]
    rw [heq]
    exact div_nonneg hm' (sq_nonneg t)
  simpa [fittedLogLinearFunctional_apply, mul_comm] using hnonneg
