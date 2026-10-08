-- Prove2me | Definitions.Def_CRCD_QuantumChannelContinuity_FilterTensor
-- name    : CRCD_QuantumChannelContinuity_FilterTensor
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-08T00:01:47.05399+00:00
-- url     : https://prove2.me/theorems/93fa07da-1b35-4167-997e-78404ca05a50
-- title:
--   Tensor-product norm bounds and contractive Gram operators
-- statement:
--   For linear maps $U:A\to B$ and $V:E\to F$ between finite-dimensional complex Hilbert spaces, their tensor-product operator satisfies
--
--   $$
--   \|U\otimes V\|\le\|U\|\,\|V\|.
--   $$
--
--   In particular, tensoring either side with an identity does not increase the norm: $\|U\otimes I_E\|\le\|U\|$ and $\|I_B\otimes V\|\le\|V\|$. Here all norms are continuous-linear-map operator norms. If $\|V\|\le1$, then $V^\dagger V\le I_E$ in the positive-operator order. These inequalities also cover zero-dimensional spaces and zero operators; nontriviality is not a premise.
-- source:
--   https://github.com/JWang226/Continuity-of-regularized-channel-renyi-divergence/blob/e29274a69978bb499f00497481c6008befb0b84d/QuantumChannelContinuity/FilterTensor.lean#L20-L108

import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Trace
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Algebra.Module.LinearMapPiProd
import Definitions.Def_CRCD_QuantumChannelContinuity_Filter
import Definitions.Def_CRCD_Quantum_QuantumMechanics_QuantumChannel_part_4
import Definitions.Def_CRCD_Quantum_QuantumMechanics_QuantumState

/-
Copyright (c) 2026 Jinzhao Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzhao Wang (AI-assisted formalization)
-/



/-! # Hilbert operator-norm bounds for tensor products -/

open QuantumState QuantumChannel TensorProduct
open scoped ComplexOrder

namespace QuantumChannelContinuity

universe u
variable {A B E F : Type u} [Qudit A] [Qudit B] [Qudit E] [Qudit F]
set_option maxHeartbeats 800000

theorem adjoint_comp_le_one_of_norm_le_one (U : E →ₗ[ℂ] F)
    (hU : ‖U.toContinuousLinearMap‖ ≤ 1) : (LinearMap.adjoint U).comp U ≤ 1 := by
  apply sub_nonneg.mp
  apply (LinearMap.nonneg_iff_isPositive _).mpr
  refine ⟨LinearMap.IsSymmetric.id.sub (LinearMap.isSymmetric_adjoint_comp_self U), ?_⟩
  intro x
  have h := U.toContinuousLinearMap.le_opNorm x
  have hn : ‖U x‖ ≤ ‖x‖ := by
    exact h.trans (by simpa using mul_le_mul_of_nonneg_right hU (norm_nonneg x))
  simp only [LinearMap.sub_apply, Module.End.one_apply, LinearMap.comp_apply,
    inner_sub_left, LinearMap.adjoint_inner_left, map_sub,
    inner_self_eq_norm_sq (𝕜 := ℂ)]
  nlinarith [norm_nonneg (U x), norm_nonneg x]

/-- Tensoring an arbitrary operator with the identity does not increase its
operator norm; this includes zero-dimensional spaces and the zero operator. -/
theorem environmentMap_norm_le (U : E →ₗ[ℂ] F) :
    ‖(environmentMap (B := B) U).toContinuousLinearMap‖ ≤ ‖U.toContinuousLinearMap‖ := by
  let c := ‖U.toContinuousLinearMap‖
  have hc : 0 ≤ c := norm_nonneg U.toContinuousLinearMap
  apply ContinuousLinearMap.opNorm_le_bound _ hc
  intro x
  by_cases hc0 : c = 0
  · have hzero : U = 0 := by
      apply LinearMap.toContinuousLinearMap.injective
      exact norm_eq_zero.mp hc0
    simp [hzero, environmentMap, hc0]
  · have hnorm : ‖(((c : ℂ)⁻¹ • U).toContinuousLinearMap)‖ ≤ 1 := by
      change ‖(c : ℂ)⁻¹ • U.toContinuousLinearMap‖ ≤ 1
      rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hc]
      change c⁻¹ * c ≤ 1
      rw [inv_mul_cancel₀ hc0]
    have h := environmentMap_norm_le_one (B := B) ((c : ℂ)⁻¹ • U)
      (adjoint_comp_le_one_of_norm_le_one _ hnorm)
    have hp : ‖environmentMap (B := B) ((c : ℂ)⁻¹ • U) x‖ ≤ ‖x‖ := by
      exact ((environmentMap (B := B) ((c : ℂ)⁻¹ • U)).toContinuousLinearMap.le_opNorm x).trans
        (by simpa using mul_le_mul_of_nonneg_right h (norm_nonneg x))
    have heq : environmentMap (B := B) ((c : ℂ)⁻¹ • U) =
        (c : ℂ)⁻¹ • environmentMap (B := B) U := by
      simp [environmentMap, TensorProduct.map_smul_right]
    rw [heq, LinearMap.smul_apply, norm_smul, norm_inv,
      Complex.norm_real, Real.norm_of_nonneg hc] at hp
    have hm := mul_le_mul_of_nonneg_left hp hc
    simpa only [← mul_assoc, mul_inv_cancel₀ hc0, one_mul] using hm

theorem tensorMap_left_norm_le (U : A →ₗ[ℂ] B) :
    ‖(TensorProduct.map U (LinearMap.id : L E)).toContinuousLinearMap‖ ≤
      ‖U.toContinuousLinearMap‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg U.toContinuousLinearMap)
  intro x
  have hx : TensorProduct.comm ℂ B E (TensorProduct.map U (LinearMap.id : L E) x) =
      environmentMap (B := E) U (TensorProduct.comm ℂ A E x) := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [environmentMap]
    | add x y hx hy => simp only [map_add, hx, hy]
  change ‖TensorProduct.map U (LinearMap.id : L E) x‖ ≤ ‖U.toContinuousLinearMap‖ * ‖x‖
  calc
    _ = ‖TensorProduct.comm ℂ B E (TensorProduct.map U (LinearMap.id : L E) x)‖ :=
      (TensorProduct.norm_comm _).symm
    _ = ‖environmentMap (B := E) U (TensorProduct.comm ℂ A E x)‖ := congrArg norm hx
    _ ≤ ‖(environmentMap (B := E) U).toContinuousLinearMap‖ *
        ‖TensorProduct.comm ℂ A E x‖ :=
      (environmentMap (B := E) U).toContinuousLinearMap.le_opNorm _
    _ ≤ ‖U.toContinuousLinearMap‖ * ‖x‖ := by
      rw [TensorProduct.norm_comm]
      exact mul_le_mul_of_nonneg_right (environmentMap_norm_le (B := E) U) (norm_nonneg x)

/-- Operator norms are submultiplicative under tensor products, on the
actual Hilbert tensor product used by the quantum-channel construction. -/
theorem tensorMap_norm_le (U : A →ₗ[ℂ] B) (V : E →ₗ[ℂ] F) :
    ‖(TensorProduct.map U V).toContinuousLinearMap‖ ≤
      ‖U.toContinuousLinearMap‖ * ‖V.toContinuousLinearMap‖ := by
  have heq : TensorProduct.map U V = (environmentMap (B := B) V).comp
      (TensorProduct.map U (LinearMap.id : L E)) := by
    simp only [environmentMap, ← TensorProduct.map_comp, LinearMap.id_comp,
      LinearMap.comp_id]
  rw [heq]
  change ‖(environmentMap (B := B) V).toContinuousLinearMap.comp
      (TensorProduct.map U (LinearMap.id : L E)).toContinuousLinearMap‖ ≤ _
  calc
    _ ≤ ‖(environmentMap (B := B) V).toContinuousLinearMap‖ *
        ‖(TensorProduct.map U (LinearMap.id : L E)).toContinuousLinearMap‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖V.toContinuousLinearMap‖ * ‖U.toContinuousLinearMap‖ :=
      mul_le_mul (environmentMap_norm_le (B := B) V) (tensorMap_left_norm_le (E := E) U)
        (norm_nonneg (TensorProduct.map U (LinearMap.id : L E)).toContinuousLinearMap)
        (norm_nonneg V.toContinuousLinearMap)
    _ = _ := mul_comm _ _

end QuantumChannelContinuity


