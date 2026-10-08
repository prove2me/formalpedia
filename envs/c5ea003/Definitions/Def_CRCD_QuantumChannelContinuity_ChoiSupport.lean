-- Prove2me | Definitions.Def_CRCD_QuantumChannelContinuity_ChoiSupport
-- name    : CRCD_QuantumChannelContinuity_ChoiSupport
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-08T03:17:26.477886+00:00
-- url     : https://prove2.me/theorems/46dee3eb-1811-4e15-be18-f1c133e5f0a0
-- title:
--   Linear Choi maps and normalized maximally entangled inputs
-- statement:
--   For a basis $(a_i)$ of a finite-dimensional complex Hilbert space $A$, the Choi construction is linear in the superoperator and produces an operator on $B\otimes A$. Vectorizing the identity in the standard orthonormal basis gives the unnormalized vector $\Omega_A$ on $A\otimes A$. When $A$ is nonzero, define the pure Choi input by $\Omega_A/\|\Omega_A\|$. Its amplified output identifies the Choi operator up to the input-dimension normalization. The support interfaces relate Choi support inclusion to completely positive domination, and use the normalized Choi input to witness support mismatch.
-- source:
--   https://github.com/JWang226/Continuity-of-regularized-channel-renyi-divergence/blob/e29274a69978bb499f00497481c6008befb0b84d/QuantumChannelContinuity/ChoiSupport.lean#L30-L153

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
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.LinearMapPiProd
import Mathlib.Topology.Algebra.Star.Unitary
import Definitions.Def_CRCD_QuantumChannelContinuity_Channels
import Definitions.Def_CRCD_QuantumChannelContinuity_Filter
import Definitions.Def_CRCD_QuantumChannelContinuity_Foundations
import Definitions.Def_CRCD_QuantumChannelContinuity_TensorChannels
import Definitions.Def_CRCD_QuantumChannelContinuity_TensorOrder
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




/-!
# Choi support, finite channel domination, and a concrete infinite witness

The normalized vectorization of the identity is an actual pure input. Its
outputs are positive scalar multiples of the Choi operators. Thus support
inclusion yields a finite completely-positive domination constant, and its
failure supplies the explicit state witness used by the infinite branch.
-/

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy
open scoped ComplexOrder TensorProduct ENNReal

namespace QuantumChannelContinuity

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

universe u
variable {A B : Type u} [Qudit A] [Qudit B]

/-- The Choi construction is linear in the superoperator. -/
noncomputable def choiLinear {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℂ A) : T A B →ₗ[ℂ] L (B ⊗[ℂ] A) where
  toFun := choi b
  map_add' Φ Ψ := by
    simp only [choi, TensorProduct.map_add_left, LinearMap.add_comp, LinearMap.comp_add,
      LinearMap.add_apply]
  map_smul' c Φ := by
    simp only [choi, TensorProduct.map_smul_left, LinearMap.smul_comp,
      LinearMap.comp_smul, LinearMap.smul_apply, RingHom.id_apply]

@[simp] theorem choiLinear_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℂ A) (Φ : T A B) : choiLinear b Φ = choi b Φ := rfl

/-- Every operator on the output/reference tensor product has a unique
superoperator as its Choi preimage. -/
theorem choiLinear_surjective {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℂ A) : Function.Surjective (choiLinear (B := B) b) := by
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp
    (choi_injective b)
  simp only [T, L, Module.finrank_linearMap, Module.finrank_tensorProduct]
  ring

/-- Complete-positive order is exactly ordinary order of Choi operators. -/
theorem cpLe_iff_choi_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℂ A) (Φ Ψ : T A B) :
    CPLe Φ Ψ ↔ choi b Φ ≤ choi b Ψ := by
  rw [CPLe, cp_iff_choi b, ChoiPositive]
  change 0 ≤ choiLinear b (Ψ - Φ) ↔ _
  rw [map_sub, choiLinear_apply, choiLinear_apply, sub_nonneg]

/-- A positive real rescaling preserves the support relation exactly. -/
theorem suppLE_smul_iff [Nontrivial B] (ρ σ : L B) {c : ℂ} (hc : c ≠ 0) :
    suppLE (c • ρ) (c • σ) ↔ suppLE ρ σ := by
  simp only [suppLE, LinearMap.ker_smul _ c hc]

/-- Scaling a vector scales its rank-one operator by the squared real scalar. -/
theorem outer_product_real_smul (v : A) (c : ℝ) :
    outer_product ((c : ℂ) • v) ((c : ℂ) • v) = ((c * c : ℝ) : ℂ) • outer_product v v := by
  ext x
  simp only [outer_product_eq_rankOne]
  change (inner ℂ ((c : ℂ) • v) x) • ((c : ℂ) • v) =
    ((c * c : ℝ) : ℂ) • ((inner ℂ v x) • v)
  rw [inner_smul_left, Complex.conj_ofReal, smul_smul, smul_smul, Complex.ofReal_mul]
  congr 1
  ring

variable [Nontrivial A] [Nontrivial B]

/-- Vectorization of the identity, before normalization. -/
noncomputable def choiVector (A : Type u) [Qudit A] : A ⊗[ℂ] A :=
  vec (stdOrthonormalBasis ℂ A).toBasis (LinearMap.id : L A)

theorem choiVector_ne_zero : choiVector A ≠ 0 := by
  intro h
  have he : (vecLinearEquiv (stdOrthonormalBasis ℂ A).toBasis) (LinearMap.id : L A) = 0 := h
  have hid : (LinearMap.id : L A) = 0 :=
    (vecLinearEquiv (stdOrthonormalBasis ℂ A).toBasis).injective (by simpa using he)
  obtain ⟨a, ha⟩ := exists_ne (0 : A)
  exact ha (LinearMap.congr_fun hid a)

/-- A genuine normalized maximally-entangled input on the reference copy. -/
noncomputable def choiInput (A : Type u) [Qudit A] [Nontrivial A] : PureInput (A ⊗[ℂ] A) where
  vector := ((‖choiVector A‖⁻¹ : ℝ) : ℂ) • choiVector A
  norm_one := by
    simpa only [Complex.ofReal_inv] using
      (norm_smul_inv_norm (𝕜 := ℂ) (choiVector_ne_zero (A := A)))

/-- The density of the normalized Choi input. -/
theorem choiInput_density :
    (choiInput A).density.op =
      ((‖choiVector A‖⁻¹ * ‖choiVector A‖⁻¹ : ℝ) : ℂ) •
        outer_product (choiVector A) (choiVector A) :=
  outer_product_real_smul _ _

/-- Applying a channel to the normalized Choi input gives its normalized Choi operator. -/
theorem amplifiedOutput_choiInput (N : CPTP A B) :
    (amplifiedOutput N (choiInput A).density).op =
      ((‖choiVector A‖⁻¹ * ‖choiVector A‖⁻¹ : ℝ) : ℂ) •
        choi (stdOrthonormalBasis ℂ A).toBasis N.toLinearMap := by
  change amplifyWithId N.toLinearMap _ = _
  rw [choiInput_density, map_smul]
  rfl

/-- The normalized input has exactly the support relation of the Choi pair. -/
theorem choiInput_support_iff (N M : CPTP A B) :
    suppLE (amplifiedOutput N (choiInput A).density).op
      (amplifiedOutput M (choiInput A).density).op ↔
    suppLE (choi (stdOrthonormalBasis ℂ A).toBasis N.toLinearMap)
      (choi (stdOrthonormalBasis ℂ A).toBasis M.toLinearMap) := by
  rw [amplifiedOutput_choiInput, amplifiedOutput_choiInput]
  exact suppLE_smul_iff _ _ (by
    exact_mod_cast mul_ne_zero (inv_ne_zero (norm_ne_zero_iff.mpr choiVector_ne_zero))
      (inv_ne_zero (norm_ne_zero_iff.mpr choiVector_ne_zero)))

/-- Choi support inclusion gives a finite, strictly positive CP domination constant. -/
theorem exists_cp_domination_of_choi_support (N M : CPTP A B)
    (hs : suppLE (choi (stdOrthonormalBasis ℂ A).toBasis N.toLinearMap)
      (choi (stdOrthonormalBasis ℂ A).toBasis M.toLinearMap)) :
    ∃ c : ℝ, 0 < c ∧ CPLe N.toLinearMap (c • M.toLinearMap) := by
  let b := (stdOrthonormalBasis ℂ A).toBasis
  have hN : 0 ≤ choi b N.toLinearMap := cp_to_choi b N.toLinearMap
    ⟨N.toCompletelyPositiveMap, rfl⟩
  have hM : 0 ≤ choi b M.toLinearMap := cp_to_choi b M.toLinearMap
    ⟨M.toCompletelyPositiveMap, rfl⟩
  obtain ⟨c, hc, hle⟩ := nonneg_le_smul_of_suppLE hN hM hs
  refine ⟨c, hc, (cpLe_iff_choi_le b _ _).mpr ?_⟩
  have hsmul : c • M.toLinearMap = (c : ℂ) • M.toLinearMap :=
    (IsScalarTower.algebraMap_smul ℂ c M.toLinearMap).symm
  rw [hsmul]
  change choi b N.toLinearMap ≤ choiLinear b ((c : ℂ) • M.toLinearMap)
  simpa only [map_smul, choiLinear_apply] using hle

/-- Every channel pair either has finite CP domination or an actual pure
stabilized input with support mismatch. This is an unconditional dichotomy. -/
theorem cp_domination_or_support_mismatch (N M : CPTP A B) :
    (∃ c : ℝ, 0 < c ∧ CPLe N.toLinearMap (c • M.toLinearMap)) ∨
      ∃ ψ : PureInput (A ⊗[ℂ] A),
        ¬ suppLE (amplifiedOutput N ψ.density).op (amplifiedOutput M ψ.density).op := by
  classical
  by_cases hs : suppLE (choi (stdOrthonormalBasis ℂ A).toBasis N.toLinearMap)
      (choi (stdOrthonormalBasis ℂ A).toBasis M.toLinearMap)
  · exact Or.inl (exists_cp_domination_of_choi_support N M hs)
  · exact Or.inr ⟨choiInput A, fun h => hs ((choiInput_support_iff N M).mp h)⟩

end QuantumChannelContinuity


