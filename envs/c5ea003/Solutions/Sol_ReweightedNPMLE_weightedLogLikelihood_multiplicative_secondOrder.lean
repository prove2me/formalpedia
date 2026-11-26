-- Prove2me | solution 1 for ReweightedNPMLE.weightedLogLikelihood_multiplicative_secondOrder
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T04:02:33.832637+00:00
-- url     : https://prove2.me/submissions/6109a469-5c79-4a8f-8ec7-3196214a1635

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
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Order.Filter.Finite
import Mathlib.Tactic
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_FiniteOptimizerFiber
import Definitions.Def_ReweightedNPMLE_FittedContact
import Definitions.Def_ReweightedNPMLE_FittedEnvelope
import Definitions.Def_ReweightedNPMLE_FittedHessian
import Definitions.Def_ReweightedNPMLE_FittedRegularity
import Definitions.Def_ReweightedNPMLE_SupportSensitivity
import Definitions.Def_ReweightedNPMLE_Weights
import Theorems.Thm_ReweightedNPMLE_log_one_add_secondOrder_isLittleO

/-!
# Analytic support sensitivity

This file supplies the scalar second-order likelihood expansion behind the
paper's support--sensitivity inequality.  It combines the Taylor expansion of
`log (1 + t u)` with simultaneous perturbations of the observation weights.
-/

open Set Filter Asymptotics
open Matrix
open scoped BigOperators Topology

open ReweightedNPMLE
open ReweightedNPMLE in
/-- Along a multiplicative fitted-value path `vᵢ(1+t uᵢ)` and an affine
weight path `w+t h`, the weighted log likelihood has the paper's exact
second-order expansion. -/
theorem solution {n : ℕ}
    (w h v u : Fin n → ℝ) (hv : ∀ i, 0 < v i) :
    (fun t : ℝ ↦
      weightedLogLikelihood (w + t • h) (fun i ↦ v i * (1 + t * u i)) -
        weightedLogLikelihood w v -
        t * ((∑ i, h i * Real.log (v i)) + ∑ i, w i * u i) -
        t ^ 2 * ((∑ i, h i * u i) - (1 / 2 : ℝ) * ∑ i, w i * u i ^ 2))
      =o[nhdsWithin 0 (Ioi 0)] (fun t : ℝ ↦ t ^ 2) := by
  have hlog (i : Fin n) :
      (fun t : ℝ ↦ Real.log (1 + t * u i) - t * u i +
          (t ^ 2 / 2) * u i ^ 2) =o[nhdsWithin 0 (Ioi 0)]
        (fun t : ℝ ↦ t ^ 2) :=
    log_one_add_secondOrder_isLittleO (u i)
  have hsum :
      (fun t : ℝ ↦ ∑ i, w i *
        (Real.log (1 + t * u i) - t * u i +
          (t ^ 2 / 2) * u i ^ 2)) =o[nhdsWithin 0 (Ioi 0)]
        (fun t : ℝ ↦ t ^ 2) := by
    apply IsLittleO.sum
    intro i _
    exact (hlog i).const_mul_left (w i)
  have hsmall (i : Fin n) :
      (fun t : ℝ ↦ t * h i *
        (Real.log (1 + t * u i) - t * u i)) =o[nhdsWithin 0 (Ioi 0)]
        (fun t : ℝ ↦ t ^ 2) := by
    have hd : HasDerivAt (fun t : ℝ ↦ Real.log (1 + t * u i)) (u i) 0 := by
      convert (((hasDerivAt_id 0).mul_const (u i)).const_add 1).log (by norm_num) using 1 <;>
        simp [id_eq]
    have hlo :
        (fun t : ℝ ↦ Real.log (1 + t * u i) - t * u i) =o[nhdsWithin 0 (Ioi 0)]
          (fun t : ℝ ↦ t) := by
      convert hd.isLittleO.mono nhdsWithin_le_nhds using 1 <;> simp [smul_eq_mul]
    have htO : (fun t : ℝ ↦ t * h i) =O[nhdsWithin 0 (Ioi 0)]
        (fun t : ℝ ↦ t) := by
      simpa [mul_comm] using
        (isBigO_refl (fun t : ℝ ↦ t) (nhdsWithin 0 (Ioi 0))).const_mul_left (h i)
    convert htO.mul_isLittleO hlo using 1 <;> ext t <;> ring
  have hsmallSum :
      (fun t : ℝ ↦ ∑ i, t * h i *
        (Real.log (1 + t * u i) - t * u i)) =o[nhdsWithin 0 (Ioi 0)]
        (fun t : ℝ ↦ t ^ 2) := by
    apply IsLittleO.sum
    intro i _
    exact hsmall i
  have hall := hsum.add hsmallSum
  refine hall.congr' ?_ (Filter.Eventually.of_forall fun _ ↦ rfl)
  have hden : ∀ᶠ t in nhds (0 : ℝ), ∀ i, 1 + t * u i ≠ 0 := by
    rw [Filter.eventually_all]
    intro i
    have hc : ContinuousAt (fun t : ℝ ↦ 1 + t * u i) 0 := by fun_prop
    simpa using hc.eventually_ne (y := (0 : ℝ)) (by norm_num)
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds hden] with t ht
  unfold weightedLogLikelihood
  simp_rw [Real.log_mul (hv _).ne' (ht _)]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul,
    Finset.mul_sum, Finset.sum_add_distrib]
  simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  rw [Finset.mul_sum, Finset.mul_sum]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring
