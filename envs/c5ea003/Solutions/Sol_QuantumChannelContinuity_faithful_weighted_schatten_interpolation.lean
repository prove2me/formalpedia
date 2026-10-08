-- Prove2me | solution 1 for QuantumChannelContinuity.faithful_weighted_schatten_interpolation
-- status  : ACCEPTED   (prove)
-- author  : @JWang226
-- created : 2026-10-08T04:18:08.119444+00:00
-- url     : https://prove2.me/submissions/e736468d-e072-4996-9686-80e06b6ff95e

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
import Theorems.Thm_QuantumChannelContinuity_exists_faithful_schatten_dual
import Theorems.Thm_QuantumChannelContinuity_weighted_trace_boundary

section

/-
Copyright (c) 2026 Jinzhao Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzhao Wang (AI-assisted formalization)
-/




/-! # Analytic operator powers for weighted Schatten interpolation -/

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy
open scoped ComplexOrder Topology

namespace QuantumChannelContinuity

universe u
variable {H : Type u} [Qudit H] [Nontrivial H]
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false



private theorem operatorCpow_ofReal {A : L H} (hA : IsStrictlyPositive A) (t : ℝ) :
    operatorCpow A (t : ℂ) = CFC.rpow A t := by
  rw [CFC.rpow_eq_normedSpace_exp_smul_log hA]
  unfold operatorCpow
  rw [Complex.coe_smul]

private theorem operatorCpow_zero (A : L H) : operatorCpow A 0 = 1 := by
  simp [operatorCpow]

private theorem operatorCpow_add (A : L H) (z w : ℂ) :
    operatorCpow A (z + w) = operatorCpow A z * operatorCpow A w := by
  letI : NormedAlgebra ℚ (L H) := .restrictScalars ℚ ℂ (L H)
  unfold operatorCpow
  rw [add_smul]
  exact NormedSpace.exp_add_of_commute (((Commute.refl (CFC.log A)).smul_left z).smul_right w)

private theorem star_operatorCpow (A : L H) (z : ℂ) :
    star (operatorCpow A z) = operatorCpow A (star z) := by
  unfold operatorCpow
  have hlog : IsSelfAdjoint (CFC.log A) := cfc_predicate _ _
  rw [NormedSpace.star_exp, star_smul, hlog.star_eq]





private theorem differentiable_operatorCpow (A : L H) : Differentiable ℂ (operatorCpow A) := by
  intro z
  exact (hasDerivAt_exp_smul_const (CFC.log A) z).differentiableAt

private theorem operatorCpow_imaginary_mem_unitary (A : L H) (t : ℝ) :
    operatorCpow A ((t : ℂ) * Complex.I) ∈ unitary (L H) := by
  rw [Unitary.mem_iff, star_operatorCpow, ← operatorCpow_add, ← operatorCpow_add]
  have hneg : star ((t : ℂ) * Complex.I) = -((t : ℂ) * Complex.I) := by simp
  simp [hneg, operatorCpow_zero]

/-- Imaginary powers do not change the operator norm. -/
private theorem norm_operatorCpow_eq_re (A : L H) (z : ℂ) :
    ‖operatorCpow A z‖ = ‖operatorCpow A (z.re : ℂ)‖ := by
  conv_lhs => rw [← Complex.re_add_im z]
  rw [operatorCpow_add]
  exact CStarRing.norm_mul_mem_unitary _ (operatorCpow_imaginary_mem_unitary A z.im)

/-- The complex power has bounded norm on every closed vertical strip.
This uses compactness only in the real direction. -/
private theorem operatorCpow_norm_bounded (A : L H) (a b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖operatorCpow A z‖ ≤ C := by
  have hc : Continuous (fun t : ℝ => ‖operatorCpow A (t : ℂ)‖) :=
    ((differentiable_operatorCpow A).continuous.comp Complex.continuous_ofReal).norm
  obtain ⟨C, hC⟩ := (isCompact_Icc.image hc).bddAbove
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro z hz₀ hz₁
  rw [norm_operatorCpow_eq_re]
  exact (hC ⟨z.re, ⟨hz₀, hz₁⟩, rfl⟩).trans (le_max_left _ _)

end QuantumChannelContinuity

end


section

/-
Copyright (c) 2026 Jinzhao Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzhao Wang (AI-assisted formalization)
-/



/-! # Three-lines interpolation for weighted quantum trace functionals -/

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy Set
open Complex.HadamardThreeLines
open scoped ComplexOrder Topology

namespace QuantumChannelContinuity

universe u
variable {H : Type u} [Qudit H] [Nontrivial H]
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false



private theorem stripExponent_re (a b : ℝ) (z : ℂ) :
    (stripExponent a b z).re = (1 - z.re) * a + z.re * b := by
  simp [stripExponent, Complex.mul_re]

private theorem stripExponent_re_mem (a b : ℝ) {z : ℂ} (hz : z ∈ verticalClosedStrip 0 1) :
    (stripExponent a b z).re ∈ Icc (min a b) (max a b) := by
  have hz0 : 0 ≤ z.re := hz.1
  have hz1 : z.re ≤ 1 := hz.2
  rw [stripExponent_re]
  constructor
  · have h₀ := mul_nonneg (sub_nonneg.mpr hz1) (sub_nonneg.mpr (min_le_left a b))
    have h₁ := mul_nonneg hz0 (sub_nonneg.mpr (min_le_right a b))
    nlinarith
  · have h₀ := mul_nonneg (sub_nonneg.mpr hz1) (sub_nonneg.mpr (le_max_left a b))
    have h₁ := mul_nonneg hz0 (sub_nonneg.mpr (le_max_right a b))
    nlinarith



private theorem differentiable_operatorTraceFamily (X σ V R : L H) (a₀ a₁ b₀ b₁ : ℝ) :
    Differentiable ℂ (operatorTraceFamily X σ V R a₀ a₁ b₀ b₁) := by
  have ha : Differentiable ℂ (stripExponent a₀ a₁) := by unfold stripExponent; fun_prop
  have hb : Differentiable ℂ (stripExponent b₀ b₁) := by unfold stripExponent; fun_prop
  have hprod := ((((differentiable_operatorCpow X).comp ha).mul_const V).mul_const R).mul
    ((differentiable_operatorCpow σ).comp hb)
  exact Tr.toContinuousLinearMap.differentiable.comp hprod

private theorem operatorTraceFamily_bounded (X σ V R : L H) (a₀ a₁ b₀ b₁ : ℝ) :
    BddAbove ((norm ∘ operatorTraceFamily X σ V R a₀ a₁ b₀ b₁) '' verticalClosedStrip 0 1) := by
  obtain ⟨C, hC, hX⟩ := operatorCpow_norm_bounded X (min a₀ a₁) (max a₀ a₁)
  obtain ⟨D, hD, hσ⟩ := operatorCpow_norm_bounded σ (min b₀ b₁) (max b₀ b₁)
  refine ⟨‖(Tr : L H →ₗ[ℂ] ℂ).toContinuousLinearMap‖ * (C * ‖V‖ * ‖R‖ * D), ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  have hzX := stripExponent_re_mem a₀ a₁ hz
  have hzσ := stripExponent_re_mem b₀ b₁ hz
  change ‖Tr (operatorCpow X (stripExponent a₀ a₁ z) * V * R *
    operatorCpow σ (stripExponent b₀ b₁ z))‖ ≤ _
  calc
    _ ≤ ‖(Tr : L H →ₗ[ℂ] ℂ).toContinuousLinearMap‖ *
        ‖operatorCpow X (stripExponent a₀ a₁ z) * V * R * operatorCpow σ (stripExponent b₀ b₁ z)‖ :=
      Tr.toContinuousLinearMap.le_opNorm _
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      calc
        _ ≤ (‖operatorCpow X (stripExponent a₀ a₁ z)‖ * ‖V‖ * ‖R‖) *
            ‖operatorCpow σ (stripExponent b₀ b₁ z)‖ := by
          exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
            ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)))
            (norm_nonneg _))
        _ ≤ _ := mul_le_mul
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (hX _ hzX.1 hzX.2) (norm_nonneg _)) (norm_nonneg _))
          (hσ _ hzσ.1 hzσ.2) (norm_nonneg _) (by positivity)

/-- Analyticity and strip boundedness are proved for the actual operator
family. Only its concrete two boundary estimates are needed by Hadamard. -/
private theorem operatorTraceFamily_three_lines (X σ V R : L H) (a₀ a₁ b₀ b₁ : ℝ)
    {θ M₀ M₁ : ℝ} (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1)
    (hleft : ∀ z : ℂ, z.re = 0 → ‖operatorTraceFamily X σ V R a₀ a₁ b₀ b₁ z‖ ≤ M₀)
    (hright : ∀ z : ℂ, z.re = 1 → ‖operatorTraceFamily X σ V R a₀ a₁ b₀ b₁ z‖ ≤ M₁) :
    ‖operatorTraceFamily X σ V R a₀ a₁ b₀ b₁ (θ : ℂ)‖ ≤ M₀ ^ (1 - θ) * M₁ ^ θ := by
  have h := norm_le_interp_of_mem_verticalClosedStrip' (by norm_num : (0 : ℝ) < 1)
    (show (θ : ℂ) ∈ verticalClosedStrip 0 1 from ⟨hθ₀, hθ₁⟩)
    (differentiable_operatorTraceFamily X σ V R a₀ a₁ b₀ b₁).diffContOnCl
    (operatorTraceFamily_bounded X σ V R a₀ a₁ b₀ b₁)
    (fun z hz => hleft z hz) (fun z hz => hright z hz)
  simpa using h

end QuantumChannelContinuity

end


section

/-
Copyright (c) 2026 Jinzhao Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzhao Wang (AI-assisted formalization)
-/






/-! # Weighted Schatten interpolation and faithful Rényi order comparisons -/

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
/-- Weighted interpolation between any two Schatten exponents greater
than one. This is proved from the actual analytic trace family and dual
attainment; no operator interpolation inequality is an input. -/
theorem solution {σ R : L H}
    (hσ : IsStrictlyPositive σ) (hR : IsUnit R)
    {t₀ t₁ θ : ℝ} (ht₀ : t₀ ∈ Ioo 0 1) (ht₁ : t₁ ∈ Ioo 0 1)
    (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) :
    let t := (1 - θ) * t₀ + θ * t₁
    schattenNorm (R * CFC.rpow σ (t - 1 / 2)) (1 / t) ≤
      schattenNorm (R * CFC.rpow σ (t₀ - 1 / 2)) (1 / t₀) ^ (1 - θ) *
      schattenNorm (R * CFC.rpow σ (t₁ - 1 / 2)) (1 / t₁) ^ θ := by
  let t := (1 - θ) * t₀ + θ * t₁
  change schattenNorm (R * CFC.rpow σ (t - 1 / 2)) (1 / t) ≤ _
  have ht : t ∈ Ioo 0 1 := by
    constructor
    · have h₀ := mul_nonneg (sub_nonneg.mpr hθ₁) ht₀.1.le
      have h₁ := mul_nonneg hθ₀ ht₁.1.le
      by_cases hz : θ = 0
      · simp [t, hz, ht₀.1]
      · have hpos := mul_pos (lt_of_le_of_ne hθ₀ (Ne.symm hz)) ht₁.1
        dsimp [t]; linarith
    · have h₀ := mul_nonneg (sub_nonneg.mpr hθ₁) (sub_pos.mpr ht₀.2).le
      have h₁ := mul_nonneg hθ₀ (sub_pos.mpr ht₁.2).le
      by_cases hz : θ = 0
      · simp [t, hz, ht₀.2]
      · have hpos := mul_pos (lt_of_le_of_ne hθ₀ (Ne.symm hz)) (sub_pos.mpr ht₁.2)
        dsimp [t]; nlinarith
  have hp : 1 < 1 / t := (one_lt_div ht.1).2 ht.2
  have hC : IsUnit (R * CFC.rpow σ (t - 1 / 2)) := hR.mul (IsStrictlyPositive.rpow σ (t - 1 / 2) hσ).isUnit
  obtain ⟨X, U, hX, hTr, hdual⟩ := exists_faithful_schatten_dual hC hp
  have hF := operatorTraceFamily_three_lines X σ (star (U : L H)) R
    (1 - t₀) (1 - t₁) (t₀ - 1 / 2) (t₁ - 1 / 2) hθ₀ hθ₁
    (by
      intro z hz
      apply weighted_trace_boundary hX hσ hTr U R ((one_lt_div ht₀.1).2 ht₀.2)
      · simp [stripExponent_re, hz]
      · simp [stripExponent_re, hz])
    (by
      intro z hz
      apply weighted_trace_boundary hX hσ hTr U R ((one_lt_div ht₁.1).2 ht₁.2)
      · simp [stripExponent_re, hz]
      · simp [stripExponent_re, hz])
  have ha : stripExponent (1 - t₀) (1 - t₁) (θ : ℂ) = ((1 - t : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [stripExponent, t] <;> ring
  have hb : stripExponent (t₀ - 1 / 2) (t₁ - 1 / 2) (θ : ℂ) = ((t - 1 / 2 : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [stripExponent, t] <;> ring
  rw [operatorTraceFamily, ha, hb, operatorCpow_ofReal hX, operatorCpow_ofReal hσ] at hF
  have hdual' : ‖Tr (CFC.rpow X (1 - t) * star (U : L H) * R * CFC.rpow σ (t - 1 / 2))‖ =
      schattenNorm (R * CFC.rpow σ (t - 1 / 2)) (1 / t) := by
    simpa only [one_div_one_div, mul_assoc] using hdual
  rw [hdual'] at hF
  simpa only [one_div_one_div] using hF

end
