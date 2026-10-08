-- Prove2me | Definitions.Def_CRCD_QuantumChannelContinuity_PowerRegrouping
-- name    : CRCD_QuantumChannelContinuity_PowerRegrouping
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-08T03:48:06.878395+00:00
-- url     : https://prove2.me/theorems/a45a1393-998a-41ae-b320-f0fa00153b74
-- title:
--   Concatenating and flattening tensor powers
-- statement:
--   For a nonzero finite-dimensional complex Hilbert space $A$ and its chosen recursive tensor powers, canonical complex linear isometric equivalences identify
--   $$
--   A_m\otimes A_n\cong A_{n+m},\qquad (A_n)_m\cong A_{nm}.
--   $$
--   The first concatenates the two blocks and the second flattens $m$ blocks of length $n$. The order $n+m$ follows the source recursion. Their unit cases use the one-dimensional scalar tensor unit. These equivalences intertwine the corresponding concrete tensor powers of a channel and support the block-power divergence identities used in regularization.
-- source:
--   https://github.com/JWang226/Continuity-of-regularized-channel-renyi-divergence/blob/e29274a69978bb499f00497481c6008befb0b84d/QuantumChannelContinuity/PowerRegrouping.lean#L25-L116

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
import Definitions.Def_CRCD_QuantumChannelContinuity_TensorNaturality
import Definitions.Def_CRCD_QuantumChannelContinuity_TensorOrder
import Definitions.Def_CRCD_QuantumChannelContinuity_TensorPowers
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




/-! # Addition and multiplication of canonical channel tensor powers -/

open QuantumState QuantumChannel
open scoped ComplexOrder TensorProduct ENNReal

namespace QuantumChannelContinuity

set_option maxHeartbeats 1500000
set_option maxRecDepth 8192
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false

variable {A B : Type} [Qudit A] [Qudit B] [Nontrivial A] [Nontrivial B]

noncomputable def unitLeftIso (A : Type) [Qudit A] :
    EuclideanSpace ℂ (Fin 1) ⊗[ℂ] A ≃ₗᵢ[ℂ] A :=
  (TensorProduct.congrIsometry tensorUnitIso (LinearIsometryEquiv.refl ℂ A)).trans
    (TensorProduct.lidIsometry ℂ A)

@[simp] theorem unitLeftIso_tmul (z : EuclideanSpace ℂ (Fin 1)) (x : A) :
    unitLeftIso A (z ⊗ₜ[ℂ] x) = tensorUnitIso z • x := by simp [unitLeftIso]

@[simp] theorem unitLeftIso_symm_apply (x : A) :
    (unitLeftIso A).symm x = tensorUnitIso.symm 1 ⊗ₜ[ℂ] x := by
  simp [unitLeftIso, TensorProduct.congrIsometry_symm]

theorem isoConj_unitLeft_tensor (X : L (EuclideanSpace ℂ (Fin 1))) (Y : L A) :
    isoConj (unitLeftIso A) (TensorProduct.map X Y) =
      tensorUnitIso (X (tensorUnitIso.symm 1)) • Y := by
  ext x
  rw [isoConj_apply, unitLeftIso_symm_apply, TensorProduct.map_tmul, unitLeftIso_tmul]
  rfl

theorem tensor_unitLeft_intertwine (Φ : T A B) :
    (isoConj (unitLeftIso B)).comp (tensorSuperoperator (LinearMap.id : T _ _) Φ) =
      Φ.comp (isoConj (unitLeftIso A)) := by
  ext1 Z
  obtain ⟨z, rfl⟩ := (l_tensor_equiv (ℋ₁ := EuclideanSpace ℂ (Fin 1)) (ℋ₂ := A)).symm.surjective Z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul X Y =>
    simp only [LinearMap.comp_apply, l_tensor_equiv_symm_tmul, tensorSuperoperator_apply,
      LinearMap.id_apply, isoConj_unitLeft_tensor, map_smul]
  | add x y hx hy => simp_all

/-- Concatenate the first `m` and last `n` factors. The target index uses
`n+m` so that recursion on the first factor is definitional. -/
noncomputable def powerConcatIso (A : Type) [Qudit A] [Nontrivial A] :
    (m n : ℕ) → TensorPower A m ⊗[ℂ] TensorPower A n ≃ₗᵢ[ℂ] TensorPower A (n + m)
  | 0, n => unitLeftIso (TensorPower A n)
  | m + 1, n => (TensorProduct.assocIsometry ℂ A (TensorPower A m) (TensorPower A n)).trans
      (TensorProduct.congrIsometry (LinearIsometryEquiv.refl ℂ A) (powerConcatIso A m n))

/-- Concatenation intertwines the actual tensor product with the actual
channel power, on every input operator. -/
theorem powerConcat_intertwine (N : CPTP A B) (m n : ℕ) :
    (isoConj (powerConcatIso B m n)).comp
        (tensorChannel (channelPower N m) (channelPower N n)).toLinearMap =
      (channelPower N (n + m)).toLinearMap.comp (isoConj (powerConcatIso A m n)) := by
  induction m with
  | zero => exact tensor_unitLeft_intertwine (channelPower N n).toLinearMap
  | succ m ih =>
    exact intertwine_trans
      (TensorProduct.assocIsometry ℂ A (TensorPower A m) (TensorPower A n))
      (TensorProduct.assocIsometry ℂ B (TensorPower B m) (TensorPower B n))
      (TensorProduct.congrIsometry (LinearIsometryEquiv.refl ℂ A) (powerConcatIso A m n))
      (TensorProduct.congrIsometry (LinearIsometryEquiv.refl ℂ B) (powerConcatIso B m n))
      _ _ _
      (tensorSuperoperator_assoc_intertwine N.toLinearMap (channelPower N m).toLinearMap
        (channelPower N n).toLinearMap)
      (tensor_intertwine (LinearIsometryEquiv.refl ℂ A) (LinearIsometryEquiv.refl ℂ B)
        (powerConcatIso A m n) (powerConcatIso B m n)
        N.toLinearMap N.toLinearMap _ _ (intertwine_refl _) ih)

/-- Flatten `m` blocks each containing `n` tensor copies. -/
noncomputable def powerMulIso (A : Type) [Qudit A] [Nontrivial A] (n : ℕ) :
    (m : ℕ) → TensorPower (TensorPower A n) m ≃ₗᵢ[ℂ] TensorPower A (n * m)
  | 0 => LinearIsometryEquiv.refl ℂ _
  | m + 1 =>
      (TensorProduct.congrIsometry (LinearIsometryEquiv.refl ℂ (TensorPower A n))
        (powerMulIso A n m)).trans (powerConcatIso A n (n * m))

/-- Nested actual channel powers are unitarily equivalent to their flattened
power. No tensor-regrouping identity is assumed. -/
theorem powerMul_intertwine (N : CPTP A B) (n m : ℕ) :
    (isoConj (powerMulIso B n m)).comp (channelPower (channelPower N n) m).toLinearMap =
      (channelPower N (n * m)).toLinearMap.comp (isoConj (powerMulIso A n m)) := by
  induction m with
  | zero => exact intertwine_refl (identityChannel _).toLinearMap
  | succ m ih =>
    exact intertwine_trans
      (TensorProduct.congrIsometry (LinearIsometryEquiv.refl ℂ (TensorPower A n)) (powerMulIso A n m))
      (TensorProduct.congrIsometry (LinearIsometryEquiv.refl ℂ (TensorPower B n)) (powerMulIso B n m))
      (powerConcatIso A n (n * m)) (powerConcatIso B n (n * m))
      _ _ _
      (tensor_intertwine (LinearIsometryEquiv.refl ℂ (TensorPower A n))
        (LinearIsometryEquiv.refl ℂ (TensorPower B n)) (powerMulIso A n m) (powerMulIso B n m)
        (channelPower N n).toLinearMap (channelPower N n).toLinearMap _ _ (intertwine_refl _) ih)
      (powerConcat_intertwine N n (n * m))

theorem blockRenyi_power {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≠ 1)
    (N M : CPTP A B) (n m : ℕ) :
    blockRenyi p (channelPower N n) (channelPower M n) m = blockRenyi p N M (n * m) :=
  channelRenyi_isometry hp hp1 (powerMulIso A n m) (powerMulIso B n m)
    _ _ _ _ (powerMul_intertwine N n m) (powerMul_intertwine M n m)



end QuantumChannelContinuity


