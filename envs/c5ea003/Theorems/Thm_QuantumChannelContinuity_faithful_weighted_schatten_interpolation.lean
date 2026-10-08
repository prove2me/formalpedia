-- Prove2me | Theorems.Thm_QuantumChannelContinuity_faithful_weighted_schatten_interpolation
-- name    : QuantumChannelContinuity.faithful_weighted_schatten_interpolation
-- status  : Proved
-- author  : @JWang226
-- created : 2026-10-08T04:18:00.165997+00:00
-- url     : https://prove2.me/theorems/3a17a4c6-0eb7-4bf9-89db-63f9dca7e62a
-- title:
--   Weighted Schatten norms interpolate between reciprocal exponents
-- statement:
--   Let $\sigma$ be positive definite and $R$ invertible on a nonzero finite-dimensional complex Hilbert space. Let $t_0,t_1\in(0,1)$, $0\le\theta\le1$, and $t=(1-\theta)t_0+\theta t_1$. Then
--
--   $$\|R\sigma^{t-1/2}\|_{1/t}\le\|R\sigma^{t_0-1/2}\|_{1/t_0}^{1-\theta}\|R\sigma^{t_1-1/2}\|_{1/t_1}^{\theta}.$$
--
--   The Schatten norms are defined by functional-calculus trace powers. This follows from the bounded analytic trace family and attained dual pairing and establishes log-convexity in reciprocal order.
-- source:
--   https://github.com/JWang226/Continuity-of-regularized-channel-renyi-divergence/blob/e29274a69978bb499f00497481c6008befb0b84d/QuantumChannelContinuity/StateOrderFaithful.lean#L45-L96

import Mathlib.Algebra.Central.End
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Complex.Hadamard
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
import Definitions.Def_CRCD_QuantumChannelContinuity_Schatten
import Definitions.Def_CRCD_QuantumChannelContinuity_StabilizedSchatten
import Definitions.Def_CRCD_QuantumChannelContinuity_StateOrderDuality
import Definitions.Def_CRCD_QuantumChannelContinuity_StateOrderInterpolation
import Definitions.Def_CRCD_QuantumChannelContinuity_StateOrderPowers
import Definitions.Def_CRCD_QuantumChannelContinuity_StateSupportLimits
import Definitions.Def_CRCD_QuantumChannelContinuity_TensorChannels
import Definitions.Def_CRCD_QuantumChannelContinuity_TensorOrder

/-
Copyright (c) 2026 Jinzhao Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzhao Wang (AI-assisted formalization)
-/






/-! # Weighted Schatten interpolation and faithful Rényi order comparisons -/

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy Set
open scoped ComplexOrder Topology

namespace QuantumChannelContinuity
end QuantumChannelContinuity
open QuantumChannelContinuity
universe u
variable {H : Type u} [Qudit H] [Nontrivial H]
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

theorem QuantumChannelContinuity.faithful_weighted_schatten_interpolation {σ R : L H}
    (hσ : IsStrictlyPositive σ) (hR : IsUnit R)
    {t₀ t₁ θ : ℝ} (ht₀ : t₀ ∈ Ioo 0 1) (ht₁ : t₁ ∈ Ioo 0 1)
    (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) :
    let t := (1 - θ) * t₀ + θ * t₁
    schattenNorm (R * CFC.rpow σ (t - 1 / 2)) (1 / t) ≤
      schattenNorm (R * CFC.rpow σ (t₀ - 1 / 2)) (1 / t₀) ^ (1 - θ) *
      schattenNorm (R * CFC.rpow σ (t₁ - 1 / 2)) (1 / t₁) ^ θ := by sorry
