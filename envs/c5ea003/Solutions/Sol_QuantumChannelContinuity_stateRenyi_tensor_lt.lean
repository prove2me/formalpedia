-- Prove2me | solution 1 for QuantumChannelContinuity.stateRenyi_tensor_lt
-- status  : ACCEPTED   (prove)
-- author  : @JWang226
-- created : 2026-10-08T04:07:39.413993+00:00
-- url     : https://prove2.me/submissions/64e54b68-595b-492d-b887-a9a4799482a7

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

/-- The finite formula below one uses nonzero overlap, not support inclusion. -/
private theorem stateRenyi_eq_formula_lt {p : ℝ} (hp : p < 1)
    (ρ σ : DensityState A) (hQ : (sandwichedQuasi p ρ.op σ.op).re ≠ 0) :
    stateRenyi p ρ σ =
      ((1 / (p - 1)) * Real.logb 2 (sandwichedQuasi p ρ.op σ.op).re : ℝ) := by
  simp only [stateRenyi, sandwichedRenyiDivNN, not_lt.mpr hp.le, false_and,
    hQ, and_false, or_false, ↓reduceIte, toBits_coe]
  rw [sandwichedRenyiDiv, ρ.trace_one]
  simp only [Complex.one_re, div_one, Real.logb]
  congr 1
  ring

private theorem stateRenyi_eq_top_of_zero_quasi {p : ℝ} (hp : p < 1)
    (ρ σ : DensityState A) (hQ : (sandwichedQuasi p ρ.op σ.op).re = 0) :
    stateRenyi p ρ σ = ⊤ := by
  simp [stateRenyi, sandwichedRenyiDivNN, hp, ρ.op_ne_zero, hQ]

end QuantumChannelContinuity

open QuantumChannelContinuity
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
universe u
variable {A B : Type u} [Qudit A] [Qudit B] [Nontrivial A] [Nontrivial B]
open QuantumChannelContinuity in
/-- Tensor additivity below one, including orthogonal-support infinities. -/
theorem solution {p : ℝ} (hhalf : 1 / 2 ≤ p) (hp : p < 1)
    (ρ σ : DensityState A) (τ ω : DensityState B) :
    stateRenyi p (ρ.tensor τ) (σ.tensor ω) = stateRenyi p ρ σ + stateRenyi p τ ω := by
  have hQ : (sandwichedQuasi p (ρ.tensor τ).op (σ.tensor ω).op).re =
      (sandwichedQuasi p ρ.op σ.op).re * (sandwichedQuasi p τ.op ω.op).re := by
    simp only [DensityState.tensor, sandwichedQuasi_tensor p _ _ _ _
      ρ.nonneg σ.nonneg τ.nonneg ω.nonneg, Complex.mul_re,
      sandwichedQuasi_im_zero, zero_mul, sub_zero]
  by_cases hρQ : (sandwichedQuasi p ρ.op σ.op).re = 0
  · have hprod : (sandwichedQuasi p (ρ.tensor τ).op (σ.tensor ω).op).re = 0 := by
      rw [hQ, hρQ, zero_mul]
    rw [stateRenyi_eq_top_of_zero_quasi hp _ _ hprod,
      stateRenyi_eq_top_of_zero_quasi hp ρ σ hρQ]
    exact (EReal.top_add_of_ne_bot
      (ne_bot_of_le_ne_bot (by simp) (stateRenyi_nonneg hhalf hp.ne τ ω))).symm
  · by_cases hτQ : (sandwichedQuasi p τ.op ω.op).re = 0
    · have hprod : (sandwichedQuasi p (ρ.tensor τ).op (σ.tensor ω).op).re = 0 := by
        rw [hQ, hτQ, mul_zero]
      rw [stateRenyi_eq_top_of_zero_quasi hp _ _ hprod,
        stateRenyi_eq_top_of_zero_quasi hp τ ω hτQ]
      exact (EReal.add_top_of_ne_bot
        (ne_bot_of_le_ne_bot (by simp) (stateRenyi_nonneg hhalf hp.ne ρ σ))).symm
    · have hprod : (sandwichedQuasi p (ρ.tensor τ).op (σ.tensor ω).op).re ≠ 0 := by
        rw [hQ]
        exact mul_ne_zero hρQ hτQ
      rw [stateRenyi_eq_formula_lt hp _ _ hprod,
        stateRenyi_eq_formula_lt hp ρ σ hρQ, stateRenyi_eq_formula_lt hp τ ω hτQ,
        hQ, Real.logb_mul hρQ hτQ, mul_add, EReal.coe_add]

end
