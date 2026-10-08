-- Prove2me | Definitions.Def_CRCD_QuantumChannelContinuity_Filter
-- name    : CRCD_QuantumChannelContinuity_Filter
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T23:55:12.581989+00:00
-- url     : https://prove2.me/theorems/6a114603-8f22-4b50-85fe-01be2c2f58f9
-- title:
--   Completely positive order and environmental filters
-- statement:
--   For superoperators $\Phi,\Psi$, write $\Phi\le_{\mathrm{CP}}\Psi$ when $\Psi-\Phi$ is completely positive at every matrix amplification. A rectangular dilation $V:A\to B\otimes E$ determines
--   $$
--   \Phi_V(X)=\operatorname{Tr}_E(VXV^*).
--   $$
--   An environmental map $U:E\to F$ acts on the dilation as $(I_B\otimes U)V$. These interfaces retain the output system and trace out only the environment. Their supporting operator identities relate environmental contractions and defects to completely positive domination and dilation error bounds; the contraction and positivity conditions are explicit in each applicable result.
-- source:
--   https://github.com/JWang226/Continuity-of-regularized-channel-renyi-divergence/blob/e29274a69978bb499f00497481c6008befb0b84d/QuantumChannelContinuity/Filter.lean#L33-L287

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
import Definitions.Def_CRCD_Quantum_QuantumMechanics_QuantumChannel_part_4
import Definitions.Def_CRCD_Quantum_QuantumMechanics_QuantumState

/-
Copyright (c) 2026 Jinzhao Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzhao Wang (AI-assisted formalization)
-/






/-!
# Concrete dilation algebra used by the fixed-environment filter

`dilationChannel` is an actual completely positive map obtained by partial
trace, using Lean-Quantum's finite-dimensional Hilbert-space definitions.
The results below verify the channel-level parallelogram inequality and the
environment-contraction step of the manuscript.  The SDP attainment theorem
in Gour (2026), equation (44), is not asserted here.
-/

open QuantumState QuantumChannel TensorProduct
open scoped ComplexOrder

namespace QuantumChannelContinuity

universe u

set_option maxHeartbeats 800000

variable {A B E F : Type u} [Qudit A] [Qudit B] [Qudit E] [Qudit F]

/-- Complete-positive order, including all matrix amplifications. -/
def CPLe (Φ Ψ : QuantumChannel.T A B) : Prop :=
  IsCompletelyPositive (Ψ - Φ)

theorem cp_add {Φ Ψ : QuantumChannel.T A B}
    (hΦ : IsCompletelyPositive Φ) (hΨ : IsCompletelyPositive Ψ) :
    IsCompletelyPositive (Φ + Ψ) := by
  apply (isCompletelyPositive_iff_cstarMatrix_nonneg _).mpr
  intro k M hM
  have hmap : M.map (Φ + Ψ) = M.map Φ + M.map Ψ := by
    ext i j x
    simp [CStarMatrix.map_apply]
  rw [hmap]
  exact add_nonneg
    ((isCompletelyPositive_iff_cstarMatrix_nonneg _).mp hΦ k M hM)
    ((isCompletelyPositive_iff_cstarMatrix_nonneg _).mp hΨ k M hM)

theorem CPLe.trans {Φ Ψ Ω : QuantumChannel.T A B}
    (hΦΨ : CPLe Φ Ψ) (hΨΩ : CPLe Ψ Ω) : CPLe Φ Ω := by
  have h := cp_add hΦΨ hΨΩ
  have hid : (Ψ - Φ) + (Ω - Ψ) = Ω - Φ := by abel
  simpa only [CPLe, hid] using h

/-- The channel associated with a rectangular dilation operator. -/
noncomputable def dilationChannel (V : A →ₗ[ℂ] B ⊗[ℂ] E) : QuantumChannel.T A B :=
  (TrRight (ℋ₂ := B) (ℋ₃ := E)).comp (krausTerm V)

theorem dilationChannel_cp (V : A →ₗ[ℂ] B ⊗[ℂ] E) :
    IsCompletelyPositive (dilationChannel V) :=
  comp_isCompletelyPositive _ _ (krausTerm_isCompletelyPositive V)
    (TrRight_isCompletelyPositive (stdOrthonormalBasis ℂ E))

/-- The parallelogram identity holds before and after the partial trace. -/
theorem dilationChannel_parallelogram (U W : A →ₗ[ℂ] B ⊗[ℂ] E) :
    (2 : ℂ) • dilationChannel U + (2 : ℂ) • dilationChannel W -
      dilationChannel (U - W) = dilationChannel (U + W) := by
  have h : (2 : ℂ) • krausTerm U + (2 : ℂ) • krausTerm W -
      krausTerm (U - W) = krausTerm (U + W) := by
    ext1 X
    simp only [LinearMap.add_apply, LinearMap.sub_apply,
      krausTerm, LinearMap.coe_mk, AddHom.coe_mk, map_add, map_sub, two_smul,
      LinearMap.add_comp, LinearMap.sub_comp, LinearMap.comp_add, LinearMap.comp_sub]
    abel
  ext1 X
  have hx := congrArg (fun T : QuantumChannel.T A (B ⊗[ℂ] E) => TrRight (T X)) h
  simpa [dilationChannel, LinearMap.comp_apply] using hx

/-- Equation `Φ_(U-W) ≤cp 2 Φ_U + 2 Φ_W`, with complete positivity proved. -/
theorem dilationChannel_sub_le (U W : A →ₗ[ℂ] B ⊗[ℂ] E) :
    CPLe (dilationChannel (U - W))
      ((2 : ℂ) • dilationChannel U + (2 : ℂ) • dilationChannel W) := by
  unfold CPLe
  rw [dilationChannel_parallelogram]
  exact dilationChannel_cp (U + W)

/-- Taking a partial trace of an elementary tensor operator. -/
theorem trRight_map (X : L B) (Y : L E) :
    TrRight (TensorProduct.map X Y) = (Tr Y) • X := by
  have hcomm : conjugateEnd (TensorProduct.comm ℂ B E) (TensorProduct.map X Y) =
      TensorProduct.map Y X := by
    ext b e
    simp [conjugateEnd]
  change Tr₂ (conjugateEnd (TensorProduct.comm ℂ B E) (TensorProduct.map X Y)) = _
  rw [hcomm, ← l_tensor_equiv_symm_tmul]
  exact Tr₂_l_tensor_equiv_symm_tmul Y X

/-- Environmental action on a dilation, leaving its output system fixed. -/
noncomputable def environmentMap (U : E →ₗ[ℂ] F) : B ⊗[ℂ] E →ₗ[ℂ] B ⊗[ℂ] F :=
  TensorProduct.map LinearMap.id U

theorem environment_kraus_map (U : E →ₗ[ℂ] F) (X : L B) (Y : L E) :
    krausTerm (environmentMap (B := B) U) (TensorProduct.map X Y) =
      TensorProduct.map X (krausTerm U Y) := by
  simp only [krausTerm, environmentMap, LinearMap.coe_mk, AddHom.coe_mk,
    TensorProduct.adjoint_map, LinearMap.adjoint_id]
  rw [← TensorProduct.map_comp, ← TensorProduct.map_comp]
  simp

/-- The discarded environmental part is itself a completely positive map.
The relation on `U,R` is the exact isometric-completion identity. -/
theorem environment_defect_identity
    (U : E →ₗ[ℂ] F) (R : L E)
    (hUR : (LinearMap.adjoint U).comp U + (LinearMap.adjoint R).comp R = 1) :
    TrRight - (TrRight (ℋ₂ := B) (ℋ₃ := F)).comp
        (krausTerm (environmentMap (B := B) U)) =
      (TrRight (ℋ₂ := B) (ℋ₃ := E)).comp
        (krausTerm (environmentMap (B := B) R)) := by
  have helem (X : L B) (Y : L E) :
      TrRight (TensorProduct.map X Y) -
        TrRight (krausTerm (environmentMap (B := B) U) (TensorProduct.map X Y)) =
      TrRight (krausTerm (environmentMap (B := B) R) (TensorProduct.map X Y)) := by
    rw [environment_kraus_map, environment_kraus_map,
      trRight_map, trRight_map, trRight_map]
    have hU : Tr (krausTerm U Y) = Tr (((LinearMap.adjoint U).comp U).comp Y) := by
      exact (LinearMap.trace_comp_comm' (U.comp Y) (LinearMap.adjoint U)).symm
    have hR : Tr (krausTerm R Y) = Tr (((LinearMap.adjoint R).comp R).comp Y) := by
      exact (LinearMap.trace_comp_comm' (R.comp Y) (LinearMap.adjoint R)).symm
    have htrace : Tr (krausTerm U Y) + Tr (krausTerm R Y) = Tr Y := by
      rw [hU, hR, ← map_add, ← LinearMap.add_comp, hUR]
      rfl
    rw [← sub_smul]
    congr 1
    exact sub_eq_iff_eq_add.mpr (by simpa [add_comm] using htrace.symm)
  ext1 Z
  obtain ⟨z, rfl⟩ := (l_tensor_equiv (ℋ₁ := B) (ℋ₂ := E)).symm.surjective Z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul X Y => simpa [l_tensor_equiv_symm_tmul] using helem X Y
  | add z w hz hw => simpa only [map_add] using congrArg₂ (· + ·) hz hw

/-- Finite-dimensional Douglas factorization, proved by extending the map on
the range of `S` by zero on its orthogonal complement.  This is the linear
algebra needed when deriving dilation alignment from a Choi/Gram inequality. -/
theorem exists_contraction_factor
    (T : A →ₗ[ℂ] F) (S : A →ₗ[ℂ] E)
    (hTS : ∀ x, ‖T x‖ ≤ ‖S x‖) :
    ∃ U : E →ₗ[ℂ] F, (LinearMap.adjoint U).comp U ≤ 1 ∧ T = U.comp S := by
  have hker : LinearMap.ker S ≤ LinearMap.ker T := by
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    apply norm_eq_zero.mp
    exact le_antisymm (by simpa [hx] using hTS x) (norm_nonneg _)
  let K := LinearMap.range S
  let D : K →ₗ[ℂ] F :=
    ((LinearMap.ker S).liftQ T hker).comp S.quotKerEquivRange.symm.toLinearMap
  have hD (x : A) : D ⟨S x, LinearMap.mem_range_self S x⟩ = T x := by
    change ((LinearMap.ker S).liftQ T hker)
      (S.quotKerEquivRange.symm ⟨S x, LinearMap.mem_range_self S x⟩) = T x
    rw [S.quotKerEquivRange_symm_apply_image]
    exact Submodule.liftQ_apply _ _ _
  have hDnorm (z : K) : ‖D z‖ ≤ ‖z‖ := by
    obtain ⟨x, hx⟩ := z.property
    have hz : z = ⟨S x, LinearMap.mem_range_self S x⟩ := Subtype.ext hx.symm
    rw [hz, hD]
    exact hTS x
  let U : E →ₗ[ℂ] F := D.comp K.orthogonalProjection.toLinearMap
  have hUnorm (x : E) : ‖U x‖ ≤ ‖x‖ :=
    (hDnorm (K.orthogonalProjection x)).trans (K.norm_orthogonalProjection_apply_le x)
  refine ⟨U, ?_, ?_⟩
  · apply sub_nonneg.mp
    apply (LinearMap.nonneg_iff_isPositive _).mpr
    refine ⟨LinearMap.IsSymmetric.id.sub (LinearMap.isSymmetric_adjoint_comp_self U), ?_⟩
    intro x
    have hn := hUnorm x
    simp only [LinearMap.sub_apply, Module.End.one_apply, LinearMap.comp_apply,
      inner_sub_left, LinearMap.adjoint_inner_left, map_sub,
      inner_self_eq_norm_sq (𝕜 := ℂ)]
    nlinarith [norm_nonneg (U x), norm_nonneg x]
  · ext x
    have hp : K.orthogonalProjection (S x) = ⟨S x, LinearMap.mem_range_self S x⟩ := by
      apply Subtype.ext
      exact K.starProjection_eq_self_iff.mpr (LinearMap.mem_range_self S x)
    change T x = D (K.orthogonalProjection (S x))
    rw [hp, hD]

/-- Douglas factorization stated directly in terms of Gram-operator order. -/
theorem exists_contraction_factor_of_gram_le
    (T : A →ₗ[ℂ] F) (S : A →ₗ[ℂ] E)
    (hTS : (LinearMap.adjoint T).comp T ≤ (LinearMap.adjoint S).comp S) :
    ∃ U : E →ₗ[ℂ] F, (LinearMap.adjoint U).comp U ≤ 1 ∧ T = U.comp S := by
  apply exists_contraction_factor T S
  intro x
  have hp := (LinearMap.nonneg_iff_isPositive _).mp (sub_nonneg.mpr hTS)
  have hx := hp.re_inner_nonneg_right x
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, inner_sub_right,
    LinearMap.adjoint_inner_right, map_sub, inner_self_eq_norm_sq (𝕜 := ℂ)] at hx
  nlinarith [norm_nonneg (T x), norm_nonneg (S x)]

/-- Every environmental contraction has a positive square-root defect. -/
theorem exists_environment_defect (U : E →ₗ[ℂ] F)
    (hU : (LinearMap.adjoint U).comp U ≤ 1) :
    ∃ R : L E, (LinearMap.adjoint U).comp U + (LinearMap.adjoint R).comp R = 1 := by
  let D : L E := 1 - (LinearMap.adjoint U).comp U
  have hD : 0 ≤ D := sub_nonneg.mpr hU
  let R : L E := CFC.sqrt D
  have hR : star R = R := (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg D)).star_eq
  have hRR : (LinearMap.adjoint R).comp R = D := by
    change star R * R = D
    rw [hR]
    exact CFC.sqrt_mul_sqrt_self D hD
  exact ⟨R, by rw [hRR]; simp [D]⟩

/-- A contraction acting only on the environment decreases partial trace in
complete-positive order.  No positivity or invertibility of its input is
assumed: complete positivity includes arbitrary reference systems. -/
theorem environment_partialTrace_cp (U : E →ₗ[ℂ] F)
    (hU : (LinearMap.adjoint U).comp U ≤ 1) :
    IsCompletelyPositive
      (TrRight - (TrRight (ℋ₂ := B) (ℋ₃ := F)).comp
        (krausTerm (environmentMap (B := B) U))) := by
  obtain ⟨R, hR⟩ := exists_environment_defect U hU
  rw [environment_defect_identity U R hR]
  exact dilationChannel_cp (environmentMap (B := B) R)

theorem krausTerm_comp (U : E →ₗ[ℂ] F) (V : A →ₗ[ℂ] E) :
    krausTerm (U.comp V) = (krausTerm U).comp (krausTerm V) := by
  ext X x
  simp [krausTerm, LinearMap.adjoint_comp]

/-- The environment-transfer domination required in the fixed-dilation
lemma, proved for arbitrary supplied dilation and contraction. -/
theorem dilationChannel_environment_le
    (U : E →ₗ[ℂ] F) (V : A →ₗ[ℂ] B ⊗[ℂ] E)
    (hU : (LinearMap.adjoint U).comp U ≤ 1) :
    CPLe (dilationChannel ((environmentMap (B := B) U).comp V))
      (dilationChannel V) := by
  unfold CPLe dilationChannel
  rw [krausTerm_comp, ← LinearMap.comp_assoc, ← LinearMap.sub_comp]
  exact comp_isCompletelyPositive _ _ (krausTerm_isCompletelyPositive V)
    (environment_partialTrace_cp U hU)

/-- Tensoring an environmental contraction with the identity remains a
contraction in the Hilbert-space operator norm. -/
theorem environmentMap_norm_le_one (U : E →ₗ[ℂ] F)
    (hU : (LinearMap.adjoint U).comp U ≤ 1) :
    ‖(environmentMap (B := B) U).toContinuousLinearMap‖ ≤ 1 := by
  obtain ⟨R, hR⟩ := exists_environment_defect U hU
  let T := environmentMap (B := B) U
  let S := environmentMap (B := B) R
  have hTS : (LinearMap.adjoint T).comp T + (LinearMap.adjoint S).comp S = 1 := by
    simp only [T, S, environmentMap, TensorProduct.adjoint_map,
      LinearMap.adjoint_id, ← TensorProduct.map_comp, LinearMap.id_comp,
      ← TensorProduct.map_add_right, hR]
    exact TensorProduct.map_id
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  have hx := congrArg (fun K : L (B ⊗[ℂ] E) => RCLike.re (inner ℂ x (K x))) hTS
  simp only [LinearMap.add_apply, LinearMap.comp_apply, Module.End.one_apply,
    inner_add_right, LinearMap.adjoint_inner_right,
    map_add, inner_self_eq_norm_sq (𝕜 := ℂ)] at hx
  change ‖T x‖ ≤ 1 * ‖x‖
  nlinarith [sq_nonneg ‖S x‖, norm_nonneg (T x), norm_nonneg x]

/-- Transferring a two-piece decomposition to a prescribed environment
preserves its operator-norm error.  The alignment equality is explicit;
its existence is the separate dilation-uniqueness theorem. -/
theorem fixed_environment_error
    (U : E →ₗ[ℂ] F) (V : A →ₗ[ℂ] B ⊗[ℂ] F)
    (X Y : A →ₗ[ℂ] B ⊗[ℂ] E)
    (hU : (LinearMap.adjoint U).comp U ≤ 1)
    (hV : (environmentMap (B := B) U).comp (X + Y) = V) :
    ‖(V - (environmentMap (B := B) U).comp X).toContinuousLinearMap‖ ≤
      ‖Y.toContinuousLinearMap‖ := by
  have hid : V - (environmentMap (B := B) U).comp X =
      (environmentMap (B := B) U).comp Y := by
    rw [← hV, LinearMap.comp_add, add_sub_cancel_left]
  rw [hid]
  change ‖(environmentMap (B := B) U).toContinuousLinearMap.comp
    Y.toContinuousLinearMap‖ ≤ ‖Y.toContinuousLinearMap‖
  calc
    _ ≤ ‖(environmentMap (B := B) U).toContinuousLinearMap‖ *
        ‖Y.toContinuousLinearMap‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * ‖Y.toContinuousLinearMap‖ := mul_le_mul_of_nonneg_right
      (environmentMap_norm_le_one (B := B) U hU) (norm_nonneg Y.toContinuousLinearMap)
    _ = _ := one_mul _



end QuantumChannelContinuity


