-- Prove2me | solution 1 for QuantumChannelContinuity.blockRenyi_tendsto_regularized
-- status  : ACCEPTED   (prove)
-- author  : @JWang226
-- created : 2026-10-08T04:12:16.196415+00:00
-- url     : https://prove2.me/submissions/cc73ee5a-5280-4067-97e0-2c8873895494

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
import Mathlib.Analysis.Subadditive
import Mathlib.Data.ENNReal.Inv
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
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_CRCD_ChannelContinuity_Testing
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
import Definitions.Def_CRCD_QuantumChannelContinuity_ChannelProducts
import Definitions.Def_CRCD_QuantumChannelContinuity_ChannelTesting
import Definitions.Def_CRCD_QuantumChannelContinuity_Channels
import Definitions.Def_CRCD_QuantumChannelContinuity_DivergenceSchatten
import Definitions.Def_CRCD_QuantumChannelContinuity_Filter
import Definitions.Def_CRCD_QuantumChannelContinuity_FilterTensor
import Definitions.Def_CRCD_QuantumChannelContinuity_Foundations
import Definitions.Def_CRCD_QuantumChannelContinuity_FoundationsDiagonal
import Definitions.Def_CRCD_QuantumChannelContinuity_FoundationsInfiniteLimit
import Definitions.Def_CRCD_QuantumChannelContinuity_FoundationsMeasurement
import Definitions.Def_CRCD_QuantumChannelContinuity_FoundationsTesting
import Definitions.Def_CRCD_QuantumChannelContinuity_FoundationsWeakTesting
import Definitions.Def_CRCD_QuantumChannelContinuity_HockeyStick
import Definitions.Def_CRCD_QuantumChannelContinuity_PowerRegrouping
import Definitions.Def_CRCD_QuantumChannelContinuity_Regularization
import Definitions.Def_CRCD_QuantumChannelContinuity_RegularizationIdentities
import Definitions.Def_CRCD_QuantumChannelContinuity_RegularizationSup
import Definitions.Def_CRCD_QuantumChannelContinuity_Schatten
import Definitions.Def_CRCD_QuantumChannelContinuity_StabilizedSchatten
import Definitions.Def_CRCD_QuantumChannelContinuity_StateSupportLimits
import Definitions.Def_CRCD_QuantumChannelContinuity_TensorChannels
import Definitions.Def_CRCD_QuantumChannelContinuity_TensorDilation
import Definitions.Def_CRCD_QuantumChannelContinuity_TensorNaturality
import Definitions.Def_CRCD_QuantumChannelContinuity_TensorOrder
import Definitions.Def_CRCD_QuantumChannelContinuity_TensorPowers
import Definitions.Def_CRCD_QuantumChannelContinuity_TensorRegrouping
import Definitions.Def_CRCD_QuantumChannelContinuity_TensorStates
import Definitions.Def_CRCD_QuantumChannelContinuity_TensorWords
import Theorems.Thm_QuantumChannelContinuity_ennreal_superadditive_tendsto_iSup_div
import Theorems.Thm_QuantumChannelContinuity_stateRenyi_tensor_lt

section

/-
Copyright (c) 2026 Jinzhao Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzhao Wang (AI-assisted formalization)
-/




/-!
# Identification of block suprema with the manuscript's limits

Tensor additivity and superadditivity also hold below one, including the
orthogonal-support infinite convention. Extended Fekete then identifies the
actual regularized quantities with their normalized block limits at every
admissible Rényi order.
-/

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy Filter
open scoped ComplexOrder TensorProduct ENNReal Topology
namespace QuantumChannelContinuity

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

universe u
variable {A B : Type u} [Qudit A] [Qudit B] [Nontrivial A] [Nontrivial B]







/-- Tensor additivity at every admissible Rényi order other than one. -/
private theorem stateRenyi_tensor_admissible {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≠ 1)
    (ρ σ : DensityState A) (τ ω : DensityState B) :
    stateRenyi p (ρ.tensor τ) (σ.tensor ω) = stateRenyi p ρ σ + stateRenyi p τ ω := by
  rcases lt_or_gt_of_ne hp1 with h | h
  · exact stateRenyi_tensor_lt hp h ρ σ τ ω
  · exact stateRenyi_tensor h ρ σ τ ω

section Channel
variable {A B C D : Type} [Qudit A] [Qudit B] [Qudit C] [Qudit D]
  [Nontrivial A] [Nontrivial B] [Nontrivial C] [Nontrivial D]

/-- Stabilized channel superadditivity at every admissible order. -/
private theorem channelRenyi_tensor_superadditive_admissible {p : ℝ}
    (hp : 1 / 2 ≤ p) (hp1 : p ≠ 1) (N M : CPTP A B) (K L : CPTP C D) :
    channelRenyi p N M + channelRenyi p K L ≤
      channelRenyi p (tensorChannel N K) (tensorChannel M L) := by
  apply ENNReal.iSup_add_iSup_le
  intro ψ φ
  have h := stateRenyi_le_channel (tensorChannel N K) (tensorChannel M L) p
    (ψ.stabilizedProduct φ)
  rw [amplifiedOutput_product N K, amplifiedOutput_product M L,
    stateRenyi_isometry hp hp1, stateRenyi_tensor_admissible hp hp1,
    EReal.toENNReal_add (stateRenyi_nonneg hp hp1 _ _) (stateRenyi_nonneg hp hp1 _ _)] at h
  exact h

private theorem blockRenyi_superadditive_admissible {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≠ 1)
    (N M : CPTP A B) (m n : ℕ) :
    blockRenyi p N M m + blockRenyi p N M n ≤ blockRenyi p N M (m + n) := by
  have h := channelRenyi_tensor_superadditive_admissible hp hp1
    (channelPower N m) (channelPower M m) (channelPower N n) (channelPower M n)
  have heq := channelRenyi_isometry hp hp1 (powerConcatIso A m n) (powerConcatIso B m n)
    (tensorChannel (channelPower N m) (channelPower N n))
    (tensorChannel (channelPower M m) (channelPower M n))
    (channelPower N (n + m)) (channelPower M (n + m))
    (powerConcat_intertwine N m n) (powerConcat_intertwine M m n)
  rw [heq] at h
  change blockRenyi p N M m + blockRenyi p N M n ≤ blockRenyi p N M (n + m) at h
  rwa [Nat.add_comm n m] at h

end Channel
end QuantumChannelContinuity

open QuantumChannelContinuity
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
universe u
variable {A B : Type u} [Qudit A] [Qudit B] [Nontrivial A] [Nontrivial B]
variable {A B C D : Type} [Qudit A] [Qudit B] [Qudit C] [Qudit D]
  [Nontrivial A] [Nontrivial B] [Nontrivial C] [Nontrivial D]
open QuantumChannelContinuity in
/-- The actual normalized Rényi block sequence converges to its defining
supremum for every admissible order, including infinite values. -/
theorem solution {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≠ 1)
    (N M : CPTP A B) :
    Tendsto (fun n : ℕ => blockRenyi p N M n / (n : ℝ≥0∞)) atTop
      (𝓝 (regularizedRenyi p N M)) :=
  ennreal_superadditive_tendsto_iSup_div (blockRenyi p N M)
    (blockRenyi_superadditive_admissible hp hp1 N M)

end
