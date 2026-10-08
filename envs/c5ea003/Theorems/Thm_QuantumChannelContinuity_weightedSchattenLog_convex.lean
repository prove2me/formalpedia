-- Prove2me | Theorems.Thm_QuantumChannelContinuity_weightedSchattenLog_convex
-- name    : QuantumChannelContinuity.weightedSchattenLog_convex
-- status  : Proved
-- author  : @JWang226
-- created : 2026-10-08T04:20:50.2489+00:00
-- url     : https://prove2.me/theorems/b15b98c1-91ff-4300-bb62-a82c544811b6
-- title:
--   The logarithmic weighted Schatten norm is convex in reciprocal order
-- statement:
--   Let $\rho,\sigma$ be positive definite operators on a nonzero finite-dimensional complex Hilbert space. The real function
--
--   $$g(t)=\log\|\rho^{1/2}\sigma^{t-1/2}\|_{1/t}$$
--
--   is convex on $(0,1)$. The Schatten norm is defined by the corresponding continuous-functional-calculus trace moment. No trace normalization is required. This convexity turns sandwiched Rényi divergence into an ordered family of secant slopes.
-- source:
--   https://github.com/JWang226/Continuity-of-regularized-channel-renyi-divergence/blob/e29274a69978bb499f00497481c6008befb0b84d/QuantumChannelContinuity/StateOrderRenyi.lean#L76-L95

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
import Mathlib.Analysis.Convex.Slope
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
import Mathlib.Data.Real.Basic
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
import Definitions.Def_CRCD_QuantumChannelContinuity_StateOrderBoundary
import Definitions.Def_CRCD_QuantumChannelContinuity_StateOrderDuality
import Definitions.Def_CRCD_QuantumChannelContinuity_StateOrderInterpolation
import Definitions.Def_CRCD_QuantumChannelContinuity_StateOrderPowers
import Definitions.Def_CRCD_QuantumChannelContinuity_StateOrderRenyi
import Definitions.Def_CRCD_QuantumChannelContinuity_StateSupportLimits
import Definitions.Def_CRCD_QuantumChannelContinuity_TensorChannels
import Definitions.Def_CRCD_QuantumChannelContinuity_TensorOrder

/-
Copyright (c) 2026 Jinzhao Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzhao Wang (AI-assisted formalization)
-/





/-! # From weighted Schatten interpolation to Rényi order monotonicity

The logarithm of the weighted Schatten norm is convex in reciprocal order.
Its value at reciprocal order one half is zero, so its secant slopes give
monotonicity of the actual sandwiched Rényi divergence on faithful states.
-/

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

theorem QuantumChannelContinuity.weightedSchattenLog_convex (ρ σ : L H)
    (hρ : IsStrictlyPositive ρ) (hσ : IsStrictlyPositive σ) :
    ConvexOn ℝ (Ioo 0 1) (weightedSchattenLog ρ σ) := by sorry
