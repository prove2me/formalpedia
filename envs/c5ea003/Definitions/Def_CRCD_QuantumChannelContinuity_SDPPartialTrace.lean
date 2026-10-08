-- Prove2me | Definitions.Def_CRCD_QuantumChannelContinuity_SDPPartialTrace
-- name    : CRCD_QuantumChannelContinuity_SDPPartialTrace
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-08T03:21:04.653747+00:00
-- url     : https://prove2.me/theorems/ffc5d0d0-be9d-4f02-bca9-496e064a5638
-- title:
--   Left partial trace and its Hermitian adjoint
-- statement:
--   On $B\otimes A$, the left partial trace discards $B$ and retains the Choi reference $A$. Its restriction to Hermitian operators is a real linear map. The dual identity-tensor map sends $Y$ on $A$ to $I_B\otimes Y$. Under the real trace pairing,
--   $$
--   \operatorname{Re}\operatorname{Tr}[(\operatorname{Tr}_B X)Y]=\operatorname{Re}\operatorname{Tr}[X(I_B\otimes Y)].
--   $$
--   The construction uses the tensor-factor swap followed by the existing right partial trace, with its complete positivity and trace-preservation proofs. These maps provide the primal and dual interfaces for the Choi slack separation argument.
-- source:
--   https://github.com/JWang226/Continuity-of-regularized-channel-renyi-divergence/blob/e29274a69978bb499f00497481c6008befb0b84d/QuantumChannelContinuity/SDPPartialTrace.lean#L23-L121

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
import Mathlib.Analysis.Convex.Cone.Dual
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
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
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
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
import Mathlib.Topology.Sequences
import Definitions.Def_CRCD_QuantumChannelContinuity_Channels
import Definitions.Def_CRCD_QuantumChannelContinuity_ChoiSupport
import Definitions.Def_CRCD_QuantumChannelContinuity_Filter
import Definitions.Def_CRCD_QuantumChannelContinuity_FilterAlignment
import Definitions.Def_CRCD_QuantumChannelContinuity_FilterSlack
import Definitions.Def_CRCD_QuantumChannelContinuity_Foundations
import Definitions.Def_CRCD_QuantumChannelContinuity_HockeyStick
import Definitions.Def_CRCD_QuantumChannelContinuity_SDPCone
import Definitions.Def_CRCD_QuantumChannelContinuity_SDPTrace
import Definitions.Def_CRCD_QuantumChannelContinuity_TensorChannels
import Definitions.Def_CRCD_QuantumChannelContinuity_TensorOrder
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




/-! # Partial-trace primal and identity-tensor dual maps for the Choi SDP -/

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy
open scoped TensorProduct ComplexOrder

namespace QuantumChannelContinuity

universe u
variable {A B : Type u} [Qudit A] [Qudit B]
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false

/-- Complete positivity preserves Hermiticity without invertibility assumptions. -/
theorem cp_map_selfAdjoint {Φ : T A B} (hΦ : IsCompletelyPositive Φ)
    {X : L A} (hX : IsSelfAdjoint X) : IsSelfAdjoint (Φ X) := by
  obtain ⟨f,rfl⟩ := hΦ
  exact hX.map f

/-- Trace out the first tensor factor, retaining the Choi reference. -/
noncomputable def leftPartialTrace : T (B ⊗[ℂ] A) A :=
  TrRight.comp (krausTerm (TensorProduct.commIsometry ℂ B A).toLinearMap)

theorem leftPartialTrace_cp : IsCompletelyPositive (leftPartialTrace (A := A) (B := B)) :=
  comp_isCompletelyPositive _ _ (krausTerm_isCompletelyPositive _) (TrRight_isCompletelyPositive (stdOrthonormalBasis ℂ B))

theorem leftPartialTrace_map (X : L B) (Y : L A) :
    leftPartialTrace (TensorProduct.map X Y) = Tr X • Y := by
  have heq : krausTerm (TensorProduct.commIsometry ℂ B A).toLinearMap (TensorProduct.map X Y) =
      TensorProduct.map Y X := by
    change (TensorProduct.commIsometry ℂ B A).toLinearMap.comp
      ((TensorProduct.map X Y).comp (LinearMap.adjoint (TensorProduct.commIsometry ℂ B A).toLinearMap)) = _
    rw [LinearIsometryEquiv.adjoint_toLinearMap_eq_symm]
    ext a b
    simp
  rw [leftPartialTrace,LinearMap.comp_apply,heq,trRight_map]

theorem trace_leftPartialTrace (X : L (B ⊗[ℂ] A)) : Tr (leftPartialTrace X) = Tr X := by
  obtain ⟨x,rfl⟩ := (l_tensor_equiv (ℋ₁ := B) (ℋ₂ := A)).symm.surjective X
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul U V =>
    rw [l_tensor_equiv_symm_tmul,leftPartialTrace_map,LinearMap.trace_tensorProduct']
    simp
  | add x y hx hy => simp_all

/-- The trace adjoint identity, on all input operators. -/
theorem leftPartialTrace_pair (X : L (B ⊗[ℂ] A)) (Y : L A) :
    Tr (Y * leftPartialTrace X) = Tr (TensorProduct.map (LinearMap.id : L B) Y * X) := by
  obtain ⟨x,rfl⟩ := (l_tensor_equiv (ℋ₁ := B) (ℋ₂ := A)).symm.surjective X
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul U V =>
    rw [l_tensor_equiv_symm_tmul,leftPartialTrace_map]
    change Tr (Y * (Tr U • V)) = Tr ((TensorProduct.map (LinearMap.id : L B) Y).comp
      (TensorProduct.map U V))
    rw [← TensorProduct.map_comp,LinearMap.id_comp,LinearMap.trace_tensorProduct']
    simp only [mul_smul_comm,map_smul,smul_eq_mul]
    rfl
  | add x y hx hy => simp_all [mul_add]

/-- The real Hermitian restriction of the primal partial trace. -/
noncomputable def hermitianLeftTrace : Hermitian (B ⊗[ℂ] A) →ₗ[ℝ] Hermitian A where
  toFun X := ⟨leftPartialTrace (X : L (B ⊗[ℂ] A)),
    cp_map_selfAdjoint (A := B ⊗[ℂ] A) (B := A) leftPartialTrace_cp X.property⟩
  map_add' := by intros; apply Subtype.ext; simp
  map_smul' := by intros; apply Subtype.ext; simp

@[simp] theorem hermitianLeftTrace_coe (X : Hermitian (B ⊗[ℂ] A)) :
    ((hermitianLeftTrace (A := A) (B := B) X : Hermitian A) : L A) = leftPartialTrace (X : L (B ⊗[ℂ] A)) := rfl

/-- The identity-tensor map dual to the partial trace. -/
noncomputable def hermitianIdentityTensor : Hermitian A →ₗ[ℝ] Hermitian (B ⊗[ℂ] A) where
  toFun Y := ⟨TensorProduct.map (LinearMap.id : L B) (Y : L A), by
    change LinearMap.adjoint (TensorProduct.map (LinearMap.id : L B) (Y : L A)) = _
    rw [TensorProduct.adjoint_map,LinearMap.adjoint_id]
    change TensorProduct.map (LinearMap.id : L B) (star (Y : L A)) = _
    rw [Y.property.star_eq]⟩
  map_add' := by intros; apply Subtype.ext; simp [TensorProduct.map_add_right]
  map_smul' := by
    intro r Y
    apply Subtype.ext
    ext b a
    simp

@[simp] theorem hermitianIdentityTensor_coe (Y : Hermitian A) :
    ((hermitianIdentityTensor (A := A) (B := B) Y : Hermitian (B ⊗[ℂ] A)) : L (B ⊗[ℂ] A)) =
      TensorProduct.map (LinearMap.id : L B) (Y : L A) := rfl

variable [Nontrivial A] [Nontrivial B]

theorem hermitianLeftTrace_trace (Q : Hermitian (B ⊗[ℂ] A)) :
    hermitianTrace (H := A) (hermitianLeftTrace (A := A) (B := B) Q) =
      hermitianTrace (H := B ⊗[ℂ] A) Q := by
  exact congrArg Complex.re (trace_leftPartialTrace (Q : L (B ⊗[ℂ] A)))

theorem hermitianLeftTrace_adjoint (Q : Hermitian (B ⊗[ℂ] A)) (Y : Hermitian A) :
    hermitianTracePair (H := A) Y (hermitianLeftTrace (A := A) (B := B) Q) =
      hermitianTracePair (H := B ⊗[ℂ] A) (hermitianIdentityTensor (A := A) (B := B) Y) Q := by
  exact congrArg Complex.re (leftPartialTrace_pair (Q : L (B ⊗[ℂ] A)) (Y : L A))

/-- Exact dual certificate when the Choi slack constraints are infeasible. -/
theorem choiSlack_separation (D : Hermitian (B ⊗[ℂ] A)) (ε : ℝ)
    (hno : ¬ ∃ Q : Hermitian (B ⊗[ℂ] A), 0 ≤ Q ∧ D ≤ Q ∧
      hermitianLeftTrace (A := A) (B := B) Q ≤ ε • (1 : Hermitian A)) :
    ∃ W : Hermitian (B ⊗[ℂ] A), ∃ Y : Hermitian A,
      0 ≤ W ∧ 0 ≤ Y ∧ W ≤ hermitianIdentityTensor (A := A) (B := B) Y ∧
      ε * hermitianTrace (H := A) Y < hermitianTracePair (H := B ⊗[ℂ] A) W D := by
  obtain ⟨W,Y,hW,hY,hle,ht⟩ := sdpSlack_separation (hermitianLeftTrace (A := A) (B := B)) (hermitianIdentityTensor (A := A) (B := B))
    hermitianLeftTrace_trace hermitianLeftTrace_adjoint D (ε • (1 : Hermitian A)) hno
  refine ⟨W,Y,hW,hY,hle,?_⟩
  simpa [hermitianTracePair, hermitianTrace] using ht

end QuantumChannelContinuity


