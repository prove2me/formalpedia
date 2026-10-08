-- Prove2me | Definitions.Def_CRCD_QuantumChannelContinuity_TensorDilation
-- name    : CRCD_QuantumChannelContinuity_TensorDilation
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-08T03:07:08.054553+00:00
-- url     : https://prove2.me/theorems/69600604-b274-4631-98b8-566639d3c557
-- title:
--   Tensor products and regrouping of dilation operators
-- statement:
--   The canonical factor isometry regroups $(B\otimes E)\otimes(D\otimes F)$ as $(B\otimes D)\otimes(E\otimes F)$, sending $(b\otimes e)\otimes(d\otimes f)$ to $(b\otimes d)\otimes(e\otimes f)$. For $U:A\to B\otimes E$ and $W:C\to D\otimes F$, define their tensor dilation by this regrouping after $U\otimes W$. Its associated channel is $\Phi_U\otimes\Phi_W$. The construction retains the full tensor environment and comes with sum, slice, pure-tensor, and norm identities used in tensor-word estimates.
-- source:
--   https://github.com/JWang226/Continuity-of-regularized-channel-renyi-divergence/blob/e29274a69978bb499f00497481c6008befb0b84d/QuantumChannelContinuity/TensorDilation.lean#L30-L142

import Mathlib.Algebra.Central.End
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Trace
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.LinearMapPiProd
import Mathlib.Topology.Algebra.Star.Unitary
import Definitions.Def_CRCD_QuantumChannelContinuity_Channels
import Definitions.Def_CRCD_QuantumChannelContinuity_Filter
import Definitions.Def_CRCD_QuantumChannelContinuity_FilterTensor
import Definitions.Def_CRCD_QuantumChannelContinuity_Foundations
import Definitions.Def_CRCD_QuantumChannelContinuity_TensorChannels
import Definitions.Def_CRCD_Quantum_QuantumEntropy_CFCDeriv
import Definitions.Def_CRCD_Quantum_QuantumEntropy_HaarUnitary
import Definitions.Def_CRCD_Quantum_QuantumEntropy_SandwichedQuasiJensen_part_3
import Definitions.Def_CRCD_Quantum_QuantumEntropy_SandwichedRenyiNonNeg_part_5
import Definitions.Def_CRCD_Quantum_QuantumEntropy_SandwichedRenyiRelativeEntropy_part_3
import Definitions.Def_CRCD_Quantum_QuantumEntropy_SandwichedRenyiUmegaki_part_2
import Definitions.Def_CRCD_Quantum_QuantumEntropy_TensorCFC
import Definitions.Def_CRCD_Quantum_QuantumEntropy_YoungInequality_part_2
import Definitions.Def_CRCD_Quantum_QuantumMechanics_QuantumChannel_part_4
import Definitions.Def_CRCD_Quantum_QuantumMechanics_QuantumState
import Definitions.Def_CRCD_Quantum_TraceInequality_BlockDiagonal
import Definitions.Def_CRCD_Quantum_TraceInequality_GeneralizedPerspectiveFunction
import Definitions.Def_CRCD_Quantum_TraceInequality_HilbertSchmidtOperatorSpace
import Definitions.Def_CRCD_Quantum_TraceInequality_JensenOperatorInequality
import Definitions.Def_CRCD_Quantum_TraceInequality_JensenOperatorInequalityIImpIV_part_2
import Definitions.Def_CRCD_Quantum_TraceInequality_LiebAndoTrace_part_2
import Definitions.Def_CRCD_Quantum_TraceInequality_LownerHeinzCore_part_3
import Definitions.Def_CRCD_Quantum_TraceInequality_LownerHeinzTheorem
import Definitions.Def_CRCD_Quantum_TraceInequality_OperatorGeometricMean

/-
Copyright (c) 2026 Jinzhao Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzhao Wang (AI-assisted formalization)
-/




/-!
# Tensor products of prescribed Stinespring dilations

The output and environment factors are regrouped by a Hilbert-space isometry.
The resulting channel is exactly the tensor product, and its operator norm is
bounded by the product of the original dilation norms.
-/

open QuantumState QuantumChannel
open scoped TensorProduct ComplexOrder

namespace QuantumChannelContinuity

universe u
variable {A B C D E F : Type u}
  [Qudit A] [Qudit B] [Qudit C] [Qudit D] [Qudit E] [Qudit F]
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false

/-- Regroup the two output factors and the two environment factors. -/
noncomputable def dilationRegroup :
    (B ⊗[ℂ] E) ⊗[ℂ] (D ⊗[ℂ] F) ≃ₗᵢ[ℂ] (B ⊗[ℂ] D) ⊗[ℂ] (E ⊗[ℂ] F) :=
  (TensorProduct.assocIsometry ℂ B E (D ⊗[ℂ] F)).trans
    ((TensorProduct.congrIsometry (LinearIsometryEquiv.refl ℂ B)
      (TensorProduct.assocIsometry ℂ E D F).symm).trans
    ((TensorProduct.congrIsometry (LinearIsometryEquiv.refl ℂ B)
      (TensorProduct.congrIsometry (TensorProduct.commIsometry ℂ E D)
        (LinearIsometryEquiv.refl ℂ F))).trans
    ((TensorProduct.congrIsometry (LinearIsometryEquiv.refl ℂ B)
      (TensorProduct.assocIsometry ℂ D E F)).trans
      (TensorProduct.assocIsometry ℂ B D (E ⊗[ℂ] F)).symm)))

@[simp] theorem dilationRegroup_tmul (b : B) (e : E) (d : D) (f : F) :
    dilationRegroup ((b ⊗ₜ[ℂ] e) ⊗ₜ[ℂ] (d ⊗ₜ[ℂ] f)) =
      (b ⊗ₜ[ℂ] d) ⊗ₜ[ℂ] (e ⊗ₜ[ℂ] f) := by
  simp [dilationRegroup]

/-- Tensor two dilations while retaining all environment degrees of freedom. -/
noncomputable def tensorDilation (U : A →ₗ[ℂ] B ⊗[ℂ] E)
    (W : C →ₗ[ℂ] D ⊗[ℂ] F) :
    A ⊗[ℂ] C →ₗ[ℂ] (B ⊗[ℂ] D) ⊗[ℂ] (E ⊗[ℂ] F) :=
  dilationRegroup.toLinearMap.comp (TensorProduct.map U W)

@[simp] theorem tensorDilation_tmul (U : A →ₗ[ℂ] B ⊗[ℂ] E)
    (W : C →ₗ[ℂ] D ⊗[ℂ] F) (a : A) (c : C) :
    tensorDilation U W (a ⊗ₜ[ℂ] c) = dilationRegroup (U a ⊗ₜ[ℂ] W c) := by
  simp [tensorDilation]

/-- Exact Kraus expansion using any chosen environment orthonormal basis. -/
theorem dilationChannel_kraus_basis {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ E) (U : A →ₗ[ℂ] B ⊗[ℂ] E) (X : L A) :
    dilationChannel U X = ∑ i, krausTerm (tensorRightSlice b i ∘ₗ U) X := by
  classical
  unfold dilationChannel
  rw [LinearMap.comp_apply, TrRight_eq_kraus_sum b]
  apply Finset.sum_congr rfl
  intro i _
  simp [krausTerm, LinearMap.adjoint_comp, LinearMap.comp_assoc]

theorem slice_dilationRegroup {ι κ : Type*} [Fintype ι] [Fintype κ]
    (b : OrthonormalBasis ι ℂ E) (c : OrthonormalBasis κ ℂ F)
    (i : ι) (j : κ) (x : B ⊗[ℂ] E) (y : D ⊗[ℂ] F) :
    tensorRightSlice (b.tensorProduct c) (i,j) (dilationRegroup (x ⊗ₜ[ℂ] y)) =
      tensorRightSlice b i x ⊗ₜ[ℂ] tensorRightSlice c j y := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul z e =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul w f =>
      simp [tensorRightSlice_tmul, TensorProduct.smul_tmul', TensorProduct.tmul_smul,
        smul_smul, mul_comm]
    | add y z hy hz => simp_all [TensorProduct.tmul_add]
  | add x y hx hy => simp_all [TensorProduct.add_tmul]

theorem tensorDilation_slice {ι κ : Type*} [Fintype ι] [Fintype κ]
    (b : OrthonormalBasis ι ℂ E) (c : OrthonormalBasis κ ℂ F)
    (U : A →ₗ[ℂ] B ⊗[ℂ] E) (W : C →ₗ[ℂ] D ⊗[ℂ] F) (i : ι) (j : κ) :
    tensorRightSlice (b.tensorProduct c) (i,j) ∘ₗ tensorDilation U W =
      TensorProduct.map (tensorRightSlice b i ∘ₗ U) (tensorRightSlice c j ∘ₗ W) := by
  ext a c'
  simp [slice_dilationRegroup]

/-- The tensor of supplied dilations realizes the tensor of their channels. -/
theorem dilationChannel_tensorDilation (U : A →ₗ[ℂ] B ⊗[ℂ] E)
    (W : C →ₗ[ℂ] D ⊗[ℂ] F) :
    dilationChannel (tensorDilation U W) =
      tensorSuperoperator (dilationChannel U) (dilationChannel W) := by
  classical
  let b := stdOrthonormalBasis ℂ E
  let c := stdOrthonormalBasis ℂ F
  apply LinearMap.ext
  intro Z
  obtain ⟨z, rfl⟩ := (l_tensor_equiv (ℋ₁ := A) (ℋ₂ := C)).symm.surjective Z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul X Y =>
    rw [l_tensor_equiv_symm_tmul, tensorSuperoperator_apply,
      dilationChannel_kraus_basis (b.tensorProduct c), dilationChannel_kraus_basis b,
      dilationChannel_kraus_basis c, Fintype.sum_prod_type]
    simp_rw [tensorDilation_slice, tensor_kraus_apply]
    ext a c'
    simp [TensorProduct.sum_tmul, TensorProduct.tmul_sum, krausTerm]
    exact Finset.sum_comm
  | add x y hx hy => simp_all

/-- Hilbert-space operator-norm submultiplicativity for the tensor dilation. -/
theorem tensorDilation_norm_le (U : A →ₗ[ℂ] B ⊗[ℂ] E)
    (W : C →ₗ[ℂ] D ⊗[ℂ] F) :
    ‖(tensorDilation U W).toContinuousLinearMap‖ ≤
      ‖U.toContinuousLinearMap‖ * ‖W.toContinuousLinearMap‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (norm_nonneg U.toContinuousLinearMap) (norm_nonneg W.toContinuousLinearMap))
  intro ψ
  change ‖dilationRegroup (TensorProduct.map U W ψ)‖ ≤ _
  rw [dilationRegroup.norm_map]
  exact ((TensorProduct.map U W).toContinuousLinearMap.le_opNorm ψ).trans
    (mul_le_mul_of_nonneg_right (tensorMap_norm_le U W) (norm_nonneg ψ))

/-- Tensor dilation is linear in the left family of summands. -/
theorem tensorDilation_sum_left {ι : Type*} [Fintype ι]
    (U : ι → A →ₗ[ℂ] B ⊗[ℂ] E) (W : C →ₗ[ℂ] D ⊗[ℂ] F) :
    tensorDilation (∑ i, U i) W = ∑ i, tensorDilation (U i) W := by
  ext a c
  simp [TensorProduct.sum_tmul]

/-- Tensor dilation is linear in the right family of summands. -/
theorem tensorDilation_sum_right {ι : Type*} [Fintype ι]
    (U : A →ₗ[ℂ] B ⊗[ℂ] E) (W : ι → C →ₗ[ℂ] D ⊗[ℂ] F) :
    tensorDilation U (∑ i, W i) = ∑ i, tensorDilation U (W i) := by
  ext a c
  simp [TensorProduct.tmul_sum]

end QuantumChannelContinuity


