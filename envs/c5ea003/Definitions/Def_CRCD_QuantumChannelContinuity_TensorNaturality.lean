-- Prove2me | Definitions.Def_CRCD_QuantumChannelContinuity_TensorNaturality
-- name    : CRCD_QuantumChannelContinuity_TensorNaturality
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-08T03:40:18.693676+00:00
-- url     : https://prove2.me/theorems/4da61425-1479-4b05-aa55-79bd16676c99
-- title:
--   Naturality of superoperators under tensor-product isometries
-- statement:
--   For finite-dimensional complex Hilbert spaces, let $\mathcal C_e(X)=eXe^\dagger$ be operator conjugation by a linear isometry equivalence. Conjugation preserves the identity and composes in the order
--
--   $$
--   \mathcal C_{e\,\mathrm{then}\,f}=\mathcal C_f\circ\mathcal C_e.
--   $$
--
--   Superoperator intertwining identities compose transitively and are preserved by tensor products: if $\mathcal C_b\circ\Phi=\Phi'\circ\mathcal C_a$ and $\mathcal C_d\circ\Psi=\Psi'\circ\mathcal C_c$, then
--
--   $$
--   \mathcal C_{b\otimes d}\circ(\Phi\otimes\Psi)=(\Phi'\otimes\Psi')\circ\mathcal C_{a\otimes c}.
--   $$
--
--   For the canonical associator $\mathfrak a:(A\otimes C)\otimes E\to A\otimes(C\otimes E)$, tensor superoperators satisfy
--
--   $$
--   \mathcal C_{\mathfrak a_{\mathrm{out}}}\circ((\Phi\otimes\Psi)\otimes\Omega)=(\Phi\otimes(\Psi\otimes\Omega))\circ\mathcal C_{\mathfrak a_{\mathrm{in}}}.
--   $$
--
--   The corresponding operator identity sends $(X\otimes Y)\otimes Z$ to $X\otimes(Y\otimes Z)$. These results apply to arbitrary superoperators, not only channels.
-- source:
--   https://github.com/JWang226/Continuity-of-regularized-channel-renyi-divergence/blob/e29274a69978bb499f00497481c6008befb0b84d/QuantumChannelContinuity/TensorNaturality.lean#L24-L96

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
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
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
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.LinearMapPiProd
import Mathlib.Topology.Algebra.Star.Unitary
import Definitions.Def_CRCD_ChannelContinuity_Testing
import Definitions.Def_CRCD_QuantumChannelContinuity_ChannelTesting
import Definitions.Def_CRCD_QuantumChannelContinuity_Channels
import Definitions.Def_CRCD_QuantumChannelContinuity_DivergenceSchatten
import Definitions.Def_CRCD_QuantumChannelContinuity_Filter
import Definitions.Def_CRCD_QuantumChannelContinuity_FilterTensor
import Definitions.Def_CRCD_QuantumChannelContinuity_Foundations
import Definitions.Def_CRCD_QuantumChannelContinuity_FoundationsDiagonal
import Definitions.Def_CRCD_QuantumChannelContinuity_FoundationsMeasurement
import Definitions.Def_CRCD_QuantumChannelContinuity_FoundationsTesting
import Definitions.Def_CRCD_QuantumChannelContinuity_FoundationsWeakTesting
import Definitions.Def_CRCD_QuantumChannelContinuity_HockeyStick
import Definitions.Def_CRCD_QuantumChannelContinuity_Regularization
import Definitions.Def_CRCD_QuantumChannelContinuity_Schatten
import Definitions.Def_CRCD_QuantumChannelContinuity_StabilizedSchatten
import Definitions.Def_CRCD_QuantumChannelContinuity_TensorChannels
import Definitions.Def_CRCD_QuantumChannelContinuity_TensorDilation
import Definitions.Def_CRCD_QuantumChannelContinuity_TensorOrder
import Definitions.Def_CRCD_QuantumChannelContinuity_TensorRegrouping
import Definitions.Def_CRCD_QuantumChannelContinuity_TensorWords
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



/-! # Naturality of tensor channels under canonical isometries -/

open QuantumState QuantumChannel
open scoped ComplexOrder TensorProduct

namespace QuantumChannelContinuity

set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false

universe u
variable {A B C D E F G H : Type u}
  [Qudit A] [Qudit B] [Qudit C] [Qudit D] [Qudit E] [Qudit F] [Qudit G] [Qudit H]

theorem isoConj_trans (e : A ≃ₗᵢ[ℂ] B) (f : B ≃ₗᵢ[ℂ] C) :
    isoConj (e.trans f) = (isoConj f).comp (isoConj e) := by
  ext X x
  simp

theorem intertwine_trans (a : A ≃ₗᵢ[ℂ] C) (b : B ≃ₗᵢ[ℂ] D)
    (c : C ≃ₗᵢ[ℂ] E) (d : D ≃ₗᵢ[ℂ] F)
    (Φ : T A B) (Ψ : T C D) (Ω : T E F)
    (h₁ : (isoConj b).comp Φ = Ψ.comp (isoConj a))
    (h₂ : (isoConj d).comp Ψ = Ω.comp (isoConj c)) :
    (isoConj (b.trans d)).comp Φ = Ω.comp (isoConj (a.trans c)) := by
  ext1 X
  have h₁x := congrArg (fun Γ => Γ X) h₁
  have h₂x := congrArg (fun Γ => Γ (isoConj a X)) h₂
  simp only [LinearMap.comp_apply] at h₁x h₂x
  simp only [isoConj_trans, LinearMap.comp_apply, h₁x, h₂x]

/-- Tensor products preserve arbitrary superoperator intertwining identities. -/
theorem tensor_intertwine (a : A ≃ₗᵢ[ℂ] E) (b : B ≃ₗᵢ[ℂ] F)
    (c : C ≃ₗᵢ[ℂ] G) (d : D ≃ₗᵢ[ℂ] H)
    (Φ : T A B) (Φ' : T E F) (Ψ : T C D) (Ψ' : T G H)
    (hΦ : (isoConj b).comp Φ = Φ'.comp (isoConj a))
    (hΨ : (isoConj d).comp Ψ = Ψ'.comp (isoConj c)) :
    (isoConj (TensorProduct.congrIsometry b d)).comp (tensorSuperoperator Φ Ψ) =
      (tensorSuperoperator Φ' Ψ').comp (isoConj (TensorProduct.congrIsometry a c)) := by
  ext1 Z
  obtain ⟨z, rfl⟩ := (l_tensor_equiv (ℋ₁ := A) (ℋ₂ := C)).symm.surjective Z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul X Y =>
    simp only [LinearMap.comp_apply, l_tensor_equiv_symm_tmul,
      tensorSuperoperator_apply, isoConj_tensor]
    have hΦx := congrArg (fun Γ => Γ X) hΦ
    have hΨy := congrArg (fun Γ => Γ Y) hΨ
    simp only [LinearMap.comp_apply] at hΦx hΨy
    rw [hΦx, hΨy]
  | add x y hx hy => simp_all

@[simp] theorem isoConj_refl (X : L A) : isoConj (LinearIsometryEquiv.refl ℂ A) X = X := by
  ext x
  simp
  rfl

theorem intertwine_refl (Φ : T A B) :
    (isoConj (LinearIsometryEquiv.refl ℂ B)).comp Φ =
      Φ.comp (isoConj (LinearIsometryEquiv.refl ℂ A)) := by ext1 X; simp

theorem isoConj_assoc (X : L A) (Y : L B) (Z : L C) :
    isoConj (TensorProduct.assocIsometry ℂ A B C) (TensorProduct.map (TensorProduct.map X Y) Z) =
      TensorProduct.map X (TensorProduct.map Y Z) := by
  ext x y z
  simp [TensorProduct.map_tmul]

/-- Associativity of the tensor product of actual superoperators, transported
by the canonical Hilbert-space associators. -/
theorem tensorSuperoperator_assoc_intertwine (Φ : T A B) (Ψ : T C D) (Ω : T E F) :
    (isoConj (TensorProduct.assocIsometry ℂ B D F)).comp
        (tensorSuperoperator (tensorSuperoperator Φ Ψ) Ω) =
      (tensorSuperoperator Φ (tensorSuperoperator Ψ Ω)).comp
        (isoConj (TensorProduct.assocIsometry ℂ A C E)) := by
  ext1 Z
  obtain ⟨z, rfl⟩ := (l_tensor_equiv (ℋ₁ := A ⊗[ℂ] C) (ℋ₂ := E)).symm.surjective Z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul X Y =>
    obtain ⟨x, rfl⟩ := (l_tensor_equiv (ℋ₁ := A) (ℋ₂ := C)).symm.surjective X
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul X₁ X₂ =>
      simp only [LinearMap.comp_apply, l_tensor_equiv_symm_tmul,
        tensorSuperoperator_apply, isoConj_assoc]
    | add x y hx hy => simp_all [TensorProduct.add_tmul]
  | add x y hx hy => simp_all

end QuantumChannelContinuity


