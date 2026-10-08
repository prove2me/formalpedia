-- Prove2me | solution 1 for QuantumChannelContinuity.weightedSchattenLog_convex
-- status  : ACCEPTED   (prove)
-- author  : @JWang226
-- created : 2026-10-08T04:26:20.203995+00:00
-- url     : https://prove2.me/submissions/f7aef354-ad7e-4fdc-99b3-3ee4c0ef07db

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
import Theorems.Thm_QuantumChannelContinuity_faithful_weighted_schatten_interpolation

section

/-
Copyright (c) 2026 Jinzhao Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzhao Wang (AI-assisted formalization)
-/




/-! # Faithful polar witnesses for Schatten duality -/

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy
open scoped ComplexOrder

namespace QuantumChannelContinuity

universe u
variable {H : Type u} [Qudit H] [Nontrivial H]
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

private theorem star_mul_self_strictlyPositive {C : L H} (hC : IsUnit C) :
    IsStrictlyPositive (star C * C) :=
  ⟨star_mul_self_nonneg _, hC.star.mul hC⟩







private theorem schattenWeight_pos {C : L H} (hC : IsUnit C) (p : ℝ) :
    0 < schattenWeight C p := by
  have hp : IsStrictlyPositive (CFC.rpow (star C * C) (p / 2)) :=
    IsStrictlyPositive.rpow (star C * C) (p / 2) (star_mul_self_strictlyPositive hC)
  exact trace_re_pos_of_ne_zero hp.nonneg hp.isUnit.ne_zero

private theorem schattenNorm_pos {C : L H} (hC : IsUnit C) (p : ℝ) : 0 < schattenNorm C p :=
  Real.rpow_pos_of_pos (schattenWeight_pos hC p) _





end QuantumChannelContinuity

end


section

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
universe u
variable {H : Type u} [Qudit H] [Nontrivial H]
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false











end QuantumChannelContinuity

open QuantumChannelContinuity
universe u
variable {H : Type u} [Qudit H] [Nontrivial H]
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
open QuantumChannelContinuity in
/-- Complex interpolation gives genuine log-convexity in reciprocal order. -/
theorem solution (ρ σ : L H)
    (hρ : IsStrictlyPositive ρ) (hσ : IsStrictlyPositive σ) :
    ConvexOn ℝ (Ioo 0 1) (weightedSchattenLog ρ σ) := by
  have hunit (t : ℝ) : IsUnit (CFC.rpow ρ (1 / 2 : ℝ) * CFC.rpow σ (t - 1 / 2)) :=
    (IsStrictlyPositive.rpow ρ (1 / 2 : ℝ) hρ).isUnit.mul (IsStrictlyPositive.rpow σ (t - 1 / 2) hσ).isUnit
  have hpos (t : ℝ) :
      0 < schattenNorm (CFC.rpow ρ (1 / 2 : ℝ) * CFC.rpow σ (t - 1 / 2)) (1 / t) :=
    schattenNorm_pos (hunit t) _
  refine ⟨convex_Ioo _ _, ?_⟩
  intro x hx y hy a b ha hb hab
  have hb1 : b ≤ 1 := by linarith
  have hab' : 1 - b = a := by linarith
  have h := faithful_weighted_schatten_interpolation hσ
    (show IsUnit (CFC.rpow ρ (1 / 2 : ℝ)) from (IsStrictlyPositive.rpow ρ (1 / 2 : ℝ) hρ).isUnit) hx hy hb hb1
  dsimp only at h
  have hl := Real.log_le_log (hpos ((1 - b) * x + b * y)) h
  rw [Real.log_mul (Real.rpow_pos_of_pos (hpos x) (1 - b)).ne'
    (Real.rpow_pos_of_pos (hpos y) b).ne', Real.log_rpow (hpos x), Real.log_rpow (hpos y)] at hl
  simpa only [weightedSchattenLog, smul_eq_mul, hab'] using hl

end
