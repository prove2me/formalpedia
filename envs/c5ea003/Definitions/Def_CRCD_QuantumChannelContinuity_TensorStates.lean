-- Prove2me | Definitions.Def_CRCD_QuantumChannelContinuity_TensorStates
-- name    : CRCD_QuantumChannelContinuity_TensorStates
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-08T03:40:59.485752+00:00
-- url     : https://prove2.me/theorems/943ed02a-5242-405d-8f74-f1a6e4de5e09
-- title:
--   Tensor products of normalized density states
-- statement:
--   For density states $\rho$ on $A$ and $\tau$ on $B$, define their tensor state on $A\otimes B$ with operator $\rho\otimes\tau$. Positivity of the tensor operator and the identity
--   $$
--   \operatorname{Tr}(\rho\otimes\tau)=\operatorname{Tr}\rho\,\operatorname{Tr}\tau=1
--   $$
--   provide the bundled state proofs. The associated operator-order and support identities, together with tensor factorization of the sandwiched quasi-entropy, support additivity of admissible state Rényi divergences, including the support-aware infinite branches.
-- source:
--   https://github.com/JWang226/Continuity-of-regularized-channel-renyi-divergence/blob/e29274a69978bb499f00497481c6008befb0b84d/QuantumChannelContinuity/TensorStates.lean#L24-L134

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



/-! # Tensor products of support-aware state divergences -/

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy
open scoped ComplexOrder TensorProduct ENNReal NNReal

namespace QuantumChannelContinuity

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false

universe u
variable {A B : Type u} [Qudit A] [Qudit B] [Nontrivial A] [Nontrivial B]

theorem tensor_operator_nonneg (X : L A) (Y : L B) (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    0 ≤ TensorProduct.map X Y := by
  have heq : TensorProduct.map X Y =
      star (TensorProduct.map (CFC.sqrt X) (CFC.sqrt Y)) *
        TensorProduct.map (CFC.sqrt X) (CFC.sqrt Y) := by
    rw [LinearMap.star_eq_adjoint, TensorProduct.adjoint_map]
    rw [← LinearMap.star_eq_adjoint, ← LinearMap.star_eq_adjoint,
      (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg X)).star_eq,
      (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg Y)).star_eq,
      ← TensorProduct.map_mul, CFC.sqrt_mul_sqrt_self X, CFC.sqrt_mul_sqrt_self Y]
  rw [heq]
  exact star_mul_self_nonneg _

noncomputable def DensityState.tensor (ρ : DensityState A) (τ : DensityState B) :
    DensityState (A ⊗[ℂ] B) where
  op := TensorProduct.map ρ.op τ.op
  nonneg := tensor_operator_nonneg _ _ ρ.nonneg τ.nonneg
  trace_one := by rw [LinearMap.trace_tensorProduct', ρ.trace_one, τ.trace_one, mul_one]

theorem tensor_operator_mono {X X' : L A} {Y Y' : L B}
    (hX : 0 ≤ X) (hY' : 0 ≤ Y') (hXX' : X ≤ X') (hYY' : Y ≤ Y') :
    TensorProduct.map X Y ≤ TensorProduct.map X' Y' := by
  apply sub_nonneg.mp
  have heq : TensorProduct.map X' Y' - TensorProduct.map X Y =
      TensorProduct.map (X' - X) Y' + TensorProduct.map X (Y' - Y) := by
    ext x y
    simp [TensorProduct.sub_tmul, TensorProduct.tmul_sub]
  rw [heq]
  exact add_nonneg (tensor_operator_nonneg _ _ (sub_nonneg.mpr hXX') hY')
    (tensor_operator_nonneg _ _ hX (sub_nonneg.mpr hYY'))

theorem suppLE_tensor (ρ σ : DensityState A) (τ ω : DensityState B)
    (hρ : suppLE ρ.op σ.op) (hτ : suppLE τ.op ω.op) :
    suppLE (ρ.tensor τ).op (σ.tensor ω).op := by
  obtain ⟨a, ha, hρa⟩ := nonneg_le_smul_of_suppLE ρ.nonneg σ.nonneg hρ
  obtain ⟨b, hb, hτb⟩ := nonneg_le_smul_of_suppLE τ.nonneg ω.nonneg hτ
  have hdom := tensor_operator_mono ρ.nonneg (smul_nonneg (by exact_mod_cast hb.le : (0 : ℂ) ≤ b)
    ω.nonneg) hρa hτb
  intro x hx
  apply nonneg_eq_zero_of_le_of_apply_eq_zero (ρ.tensor τ).nonneg hdom
  change TensorProduct.map ((a : ℂ) • σ.op) ((b : ℂ) • ω.op) x = 0
  rw [TensorProduct.map_smul_left, TensorProduct.map_smul_right,
    LinearMap.smul_apply, LinearMap.smul_apply]
  change (a : ℂ) • (b : ℂ) • (σ.tensor ω).op x = 0
  rw [show (σ.tensor ω).op x = 0 from hx, smul_zero, smul_zero]

theorem suppLE_tensor_iff (ρ σ : DensityState A) (τ ω : DensityState B) :
    suppLE (ρ.tensor τ).op (σ.tensor ω).op ↔ suppLE ρ.op σ.op ∧ suppLE τ.op ω.op := by
  refine ⟨?_, fun h => suppLE_tensor ρ σ τ ω h.1 h.2⟩
  intro h
  have hy : ∃ y, τ.op y ≠ 0 := by
    by_contra! hn
    exact τ.op_ne_zero (by ext y; exact hn y)
  have hx : ∃ x, ρ.op x ≠ 0 := by
    by_contra! hn
    exact ρ.op_ne_zero (by ext x; exact hn x)
  obtain ⟨y, hy⟩ := hy
  obtain ⟨x, hx⟩ := hx
  constructor
  · intro z hz
    have hzero := h (show z ⊗ₜ[ℂ] y ∈ LinearMap.ker (σ.tensor ω).op by
      change TensorProduct.map σ.op ω.op (z ⊗ₜ[ℂ] y) = 0
      simp [show σ.op z = 0 from hz])
    change ρ.op z ⊗ₜ[ℂ] τ.op y = 0 at hzero
    have hn := congrArg norm hzero
    rw [TensorProduct.norm_tmul, norm_zero] at hn
    exact norm_eq_zero.mp ((mul_eq_zero.mp hn).resolve_right (norm_ne_zero_iff.mpr hy))
  · intro z hz
    have hzero := h (show x ⊗ₜ[ℂ] z ∈ LinearMap.ker (σ.tensor ω).op by
      change TensorProduct.map σ.op ω.op (x ⊗ₜ[ℂ] z) = 0
      simp [show ω.op z = 0 from hz])
    change ρ.op x ⊗ₜ[ℂ] τ.op z = 0 at hzero
    have hn := congrArg norm hzero
    rw [TensorProduct.norm_tmul, norm_zero] at hn
    exact norm_eq_zero.mp ((mul_eq_zero.mp hn).resolve_left (norm_ne_zero_iff.mpr hx))

theorem sandwichedQuasi_im_zero (p : ℝ) (ρ σ : L A) :
    (sandwichedQuasi p ρ σ).im = 0 := by
  unfold sandwichedQuasi
  have h : 0 ≤ CFC.rpow (CFC.rpow σ ((1 - p) / (2 * p)) * ρ *
      CFC.rpow σ ((1 - p) / (2 * p))) p := CFC.rpow_nonneg
  exact (Complex.nonneg_iff.mp (((LinearMap.nonneg_iff_isPositive _).1 h).trace_nonneg)).2.symm

/-- Exact tensor additivity, including support mismatch and infinite values. -/
theorem stateRenyi_tensor {p : ℝ} (hp : 1 < p)
    (ρ σ : DensityState A) (τ ω : DensityState B) :
    stateRenyi p (ρ.tensor τ) (σ.tensor ω) = stateRenyi p ρ σ + stateRenyi p τ ω := by
  by_cases hs : suppLE ρ.op σ.op
  · by_cases ht : suppLE τ.op ω.op
    · rw [stateRenyi_eq_formula hp _ _ (suppLE_tensor ρ σ τ ω hs ht),
        stateRenyi_eq_formula hp ρ σ hs, stateRenyi_eq_formula hp τ ω ht]
      have hQρ := sandwichedQuasi_pos_of_support (p := p) (by linarith) ρ.op σ.op
        ρ.nonneg σ.nonneg hs ρ.op_ne_zero
      have hQτ := sandwichedQuasi_pos_of_support (p := p) (by linarith) τ.op ω.op
        τ.nonneg ω.nonneg ht τ.op_ne_zero
      simp only [DensityState.tensor, sandwichedQuasi_tensor p _ _ _ _
        ρ.nonneg σ.nonneg τ.nonneg ω.nonneg, Complex.mul_re,
        sandwichedQuasi_im_zero, zero_mul, sub_zero]
      rw [Real.logb_mul hQρ.ne' hQτ.ne', mul_add, EReal.coe_add]
    · have hst : ¬ suppLE (ρ.tensor τ).op (σ.tensor ω).op :=
        fun h => ht ((suppLE_tensor_iff ρ σ τ ω).mp h).2
      rw [stateRenyi_eq_top_of_not_support hp _ _ hst,
        stateRenyi_eq_top_of_not_support hp τ ω ht]
      exact (EReal.add_top_of_ne_bot
        (ne_bot_of_le_ne_bot (by simp) (stateRenyi_nonneg (by linarith) hp.ne' ρ σ))).symm
  · have hst : ¬ suppLE (ρ.tensor τ).op (σ.tensor ω).op :=
      fun h => hs ((suppLE_tensor_iff ρ σ τ ω).mp h).1
    rw [stateRenyi_eq_top_of_not_support hp _ _ hst,
      stateRenyi_eq_top_of_not_support hp ρ σ hs]
    exact (EReal.top_add_of_ne_bot
      (ne_bot_of_le_ne_bot (by simp) (stateRenyi_nonneg (by linarith) hp.ne' τ ω))).symm

end QuantumChannelContinuity


