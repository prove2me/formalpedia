-- Prove2me | Definitions.Def_CRCD_QuantumChannelContinuity_TensorPowers
-- name    : CRCD_QuantumChannelContinuity_TensorPowers
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-08T03:46:47.131982+00:00
-- url     : https://prove2.me/theorems/faa4b18e-6e3e-46e0-8196-bb918497b789
-- title:
--   The tensor unit and one-copy power isometry
-- statement:
--   The one-dimensional tensor unit is the Euclidean complex space indexed by a singleton. Its canonical orthonormal coordinate identifies it isometrically with $\mathbb C$. For a nonzero finite-dimensional complex Hilbert space $A$, this gives an isometric identification $A_1=A\otimes A_0\cong A$. The construction intertwines the recursively defined one-copy channel power with the original channel and transports the stabilized block relative divergence at length one to the ordinary channel relative divergence.
-- source:
--   https://github.com/JWang226/Continuity-of-regularized-channel-renyi-divergence/blob/e29274a69978bb499f00497481c6008befb0b84d/QuantumChannelContinuity/TensorPowers.lean#L20-L81

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



/-! # Canonical regrouping of concrete channel tensor powers -/

open QuantumState QuantumChannel
open scoped ComplexOrder TensorProduct ENNReal

namespace QuantumChannelContinuity

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false

/-- The canonical scalar coordinate on the one-dimensional tensor unit. -/
noncomputable def tensorUnitIso : EuclideanSpace ℂ (Fin 1) ≃ₗᵢ[ℂ] ℂ :=
  (OrthonormalBasis.singleton (Fin 1) ℂ).repr.symm

variable {A B : Type} [Qudit A] [Qudit B] [Nontrivial A] [Nontrivial B]

noncomputable def powerOneIso (A : Type) [Qudit A] [Nontrivial A] :
    TensorPower A 1 ≃ₗᵢ[ℂ] A :=
  (TensorProduct.congrIsometry (LinearIsometryEquiv.refl ℂ A) tensorUnitIso).trans
    ((TensorProduct.commIsometry ℂ A ℂ).trans (TensorProduct.lidIsometry ℂ A))

@[simp] theorem powerOneIso_tmul (x : A) (z : EuclideanSpace ℂ (Fin 1)) :
    powerOneIso A (x ⊗ₜ[ℂ] z) = tensorUnitIso z • x := by
  simp [powerOneIso, TensorPower, tensorPowerSpace]

@[simp] theorem powerOneIso_symm_apply (x : A) :
    (powerOneIso A).symm x = x ⊗ₜ[ℂ] tensorUnitIso.symm 1 := by
  simp [powerOneIso, TensorPower, tensorPowerSpace, TensorProduct.congrIsometry_symm]

/-- Conjugating an operator with a scalar factor into a one-copy space. -/
theorem isoConj_powerOne_tensor (X : L A) (Y : L (EuclideanSpace ℂ (Fin 1))) :
    isoConj (powerOneIso A) (TensorProduct.map X Y) =
      tensorUnitIso (Y (tensorUnitIso.symm 1)) • X := by
  ext x
  rw [isoConj_apply, powerOneIso_symm_apply]
  calc
    _ = powerOneIso A (X x ⊗ₜ[ℂ] Y (tensorUnitIso.symm 1)) :=
      congrArg (powerOneIso A) (TensorProduct.map_tmul X Y x (tensorUnitIso.symm 1))
    _ = _ := powerOneIso_tmul _ _

/-- A single canonical channel copy differs only by the tensor-unit coordinates. -/
theorem channelPower_one_intertwine (N : CPTP A B) :
    (isoConj (powerOneIso B)).comp (channelPower N 1).toLinearMap =
      N.toLinearMap.comp (isoConj (powerOneIso A)) := by
  ext1 Z
  obtain ⟨z, rfl⟩ := (l_tensor_equiv (ℋ₁ := A)
    (ℋ₂ := EuclideanSpace ℂ (Fin 1))).symm.surjective Z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul X Y =>
    change isoConj (powerOneIso B)
      (tensorSuperoperator N.toLinearMap (LinearMap.id : T _ _)
        ((l_tensor_equiv (ℋ₁ := A) (ℋ₂ := EuclideanSpace ℂ (Fin 1))).symm (X ⊗ₜ[ℂ] Y))) = _
    rw [l_tensor_equiv_symm_tmul, tensorSuperoperator_apply]
    change isoConj (powerOneIso B) (TensorProduct.map (N.toLinearMap X) Y) =
      N.toLinearMap (isoConj (powerOneIso A) (TensorProduct.map X Y))
    rw [isoConj_powerOne_tensor, isoConj_powerOne_tensor, map_smul]
  | add x y hx hy => simp_all



theorem blockRelative_one (N M : CPTP A B) :
    blockRelative N M 1 = channelRelative N M :=
  channelRelative_isometry (powerOneIso A) (powerOneIso B)
    (channelPower N 1) (channelPower M 1) N M
    (channelPower_one_intertwine N) (channelPower_one_intertwine M)

end QuantumChannelContinuity


