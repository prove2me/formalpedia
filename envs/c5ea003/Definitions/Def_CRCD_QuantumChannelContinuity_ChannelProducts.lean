-- Prove2me | Definitions.Def_CRCD_QuantumChannelContinuity_ChannelProducts
-- name    : CRCD_QuantumChannelContinuity_ChannelProducts
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-08T03:41:53.620507+00:00
-- url     : https://prove2.me/theorems/e73e9438-ffc7-4a10-86b4-a3f90647fc4f
-- title:
--   Product inputs for stabilized channel comparisons
-- statement:
--   For unit vectors $\psi\in A$ and $\varphi\in B$, their tensor product is a unit vector on $A\otimes B$. For independently stabilized inputs $\psi\in A\otimes A$ and $\varphi\in C\otimes C$, regroup their tensor product into
--   $$
--   (A\otimes C)\otimes(A\otimes C).
--   $$
--   This gives a valid pure input for the tensor-product channel, keeping the two channel systems before their reference copies. The associated density and amplified-output identities identify its output with the regrouped product of the individual stabilized outputs, enabling superadditivity of channel Rényi divergence.
-- source:
--   https://github.com/JWang226/Continuity-of-regularized-channel-renyi-divergence/blob/e29274a69978bb499f00497481c6008befb0b84d/QuantumChannelContinuity/ChannelProducts.lean#L24-L106

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
import Definitions.Def_CRCD_QuantumChannelContinuity_TensorStates
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



/-! # Product inputs and superadditivity of concrete stabilized divergences -/

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy
open scoped ComplexOrder TensorProduct ENNReal

namespace QuantumChannelContinuity

set_option maxHeartbeats 1500000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false

universe u
variable {A B C D : Type u} [Qudit A] [Qudit B] [Qudit C] [Qudit D]

@[simp] theorem dilationRegroup_symm_tmul (a : A) (b : B) (c : C) (d : D) :
    (dilationRegroup (B := A) (E := B) (D := C) (F := D)).symm
      ((a ⊗ₜ[ℂ] c) ⊗ₜ[ℂ] (b ⊗ₜ[ℂ] d)) =
      (a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] (c ⊗ₜ[ℂ] d) := by
  apply (dilationRegroup (B := A) (E := B) (D := C) (F := D)).injective
  simp

/-- Four operator tensor factors follow the same canonical regrouping as vectors. -/
theorem isoConj_regroup (X : L A) (Y : L B) (Z : L C) (W : L D) :
    isoConj dilationRegroup (TensorProduct.map (TensorProduct.map X Y) (TensorProduct.map Z W)) =
      TensorProduct.map (TensorProduct.map X Z) (TensorProduct.map Y W) := by
  ext a c b d
  simp [TensorProduct.map_tmul]

theorem outer_tensor (x x' : A) (y y' : B) :
    outer_product (x ⊗ₜ[ℂ] y) (x' ⊗ₜ[ℂ] y') =
      TensorProduct.map (outer_product x x') (outer_product y y') := by
  rw [← l_tensor_equiv_symm_outer_product, l_tensor_equiv_symm_tmul]

noncomputable def PureInput.tensor (ψ : PureInput A) (φ : PureInput B) : PureInput (A ⊗[ℂ] B) :=
  ⟨ψ.vector ⊗ₜ[ℂ] φ.vector, by rw [TensorProduct.norm_tmul, ψ.norm_one, φ.norm_one, mul_one]⟩

@[simp] theorem PureInput.density_tensor [Nontrivial A] [Nontrivial B]
    (ψ : PureInput A) (φ : PureInput B) :
    (ψ.tensor φ).density = ψ.density.tensor φ.density := by
  apply DensityState.ext
  exact outer_tensor _ _ _ _

/-- Product stabilized outputs, with the reference factors moved to the end. -/
theorem amplify_tensor_regroup (N : CPTP A B) (K : CPTP C D)
    (X : L (A ⊗[ℂ] A)) (Y : L (C ⊗[ℂ] C)) :
    amplifyWithId (tensorChannel N K).toLinearMap
        (isoConj dilationRegroup (TensorProduct.map X Y)) =
      isoConj dilationRegroup
        (TensorProduct.map (amplifyWithId N.toLinearMap X) (amplifyWithId K.toLinearMap Y)) := by
  obtain ⟨x, rfl⟩ := (l_tensor_equiv (ℋ₁ := A) (ℋ₂ := A)).symm.surjective X
  obtain ⟨y, rfl⟩ := (l_tensor_equiv (ℋ₁ := C) (ℋ₂ := C)).symm.surjective Y
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul X₁ X₂ =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul Y₁ Y₂ =>
      simp only [l_tensor_equiv_symm_tmul, isoConj_regroup, amplifyWithId_tensor]
      change TensorProduct.map (tensorSuperoperator N.toLinearMap K.toLinearMap
        (TensorProduct.map X₁ Y₁)) (TensorProduct.map X₂ Y₂) = _
      rw [tensorSuperoperator_apply]
      rfl
    | add y z hy hz => simp_all [TensorProduct.map_add_right]
  | add x z hx hz => simp_all [TensorProduct.map_add_left]

variable [Nontrivial A] [Nontrivial B] [Nontrivial C] [Nontrivial D]

/-- A product of independently optimized entangled inputs is an admissible
pure input for the tensor-product channel. -/
noncomputable def PureInput.stabilizedProduct (ψ : PureInput (A ⊗[ℂ] A))
    (φ : PureInput (C ⊗[ℂ] C)) : PureInput ((A ⊗[ℂ] C) ⊗[ℂ] (A ⊗[ℂ] C)) :=
  (ψ.tensor φ).mapIso dilationRegroup

theorem amplifiedOutput_product (N : CPTP A B) (K : CPTP C D)
    (ψ : PureInput (A ⊗[ℂ] A)) (φ : PureInput (C ⊗[ℂ] C)) :
    amplifiedOutput (tensorChannel N K) (ψ.stabilizedProduct φ).density =
      ((amplifiedOutput N ψ.density).tensor (amplifiedOutput K φ.density)).map
        (isometryChannel dilationRegroup) := by
  apply DensityState.ext
  rw [PureInput.stabilizedProduct, PureInput.density_mapIso, PureInput.density_tensor]
  exact amplify_tensor_regroup N K ψ.density.op φ.density.op

/-- Superadditivity under channel tensor products, in the actual stabilized
support-aware definitions and including infinite values. -/
theorem channelRenyi_tensor_superadditive {p : ℝ} (hp : 1 < p)
    (N M : CPTP A B) (K L : CPTP C D) :
    channelRenyi p N M + channelRenyi p K L ≤
      channelRenyi p (tensorChannel N K) (tensorChannel M L) := by
  apply ENNReal.iSup_add_iSup_le
  intro ψ φ
  have h := stateRenyi_le_channel (tensorChannel N K) (tensorChannel M L) p
    (ψ.stabilizedProduct φ)
  rw [amplifiedOutput_product N K, amplifiedOutput_product M L,
    stateRenyi_isometry (by linarith) hp.ne', stateRenyi_tensor hp,
    EReal.toENNReal_add (stateRenyi_nonneg (by linarith) hp.ne' _ _)
      (stateRenyi_nonneg (by linarith) hp.ne' _ _)] at h
  exact h

end QuantumChannelContinuity


