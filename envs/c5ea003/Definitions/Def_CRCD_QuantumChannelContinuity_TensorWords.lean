-- Prove2me | Definitions.Def_CRCD_QuantumChannelContinuity_TensorWords
-- name    : CRCD_QuantumChannelContinuity_TensorWords
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-08T03:34:37.424426+00:00
-- url     : https://prove2.me/theorems/cadd5359-6ff0-4548-93a6-9d19da7b8b98
-- title:
--   Repeated and word-indexed dilation operators
-- statement:
--   The zero-copy dilation is defined on the chosen one-dimensional tensor unit. For nonzero finite-dimensional complex Hilbert spaces $A,B,E$ and $V:A\to B\otimes E$, define its repeated dilation recursively by tensoring $V$ with the preceding power. More generally, for a family $(U_i)_{i\in\iota}$ and a word $w:\{0,\ldots,n-1\}\to\iota$, define $U_w$ by tensoring the selected letters and regrouping outputs and environments. Its domain is $A_n$ and codomain is $B_n\otimes E_n$. Thus every word retains the same concrete environment type. Sum, norm, and completely positive comparison identities support the dilation rate bounds for regularized channel divergence.
-- source:
--   https://github.com/JWang226/Continuity-of-regularized-channel-renyi-divergence/blob/e29274a69978bb499f00497481c6008befb0b84d/QuantumChannelContinuity/TensorWords.lean#L29-L231

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
# Actual tensor-word dilations

Words are tensor products of supplied dilation pieces.  Their sum realizes the
actual channel power used in `Regularization`; the domination and norm constants
are the products of the one-block constants.
-/

open QuantumState QuantumChannel
open scoped ComplexOrder TensorProduct

namespace QuantumChannelContinuity

set_option maxHeartbeats 300000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false

def DilationUnit := EuclideanSpace ℂ (Fin 1)
noncomputable instance : Qudit DilationUnit := inferInstanceAs (Qudit (EuclideanSpace ℂ (Fin 1)))

/-- The zero-copy dilation, in exactly the unit spaces used by `TensorPower`. -/
noncomputable def unitDilation : DilationUnit →ₗ[ℂ] DilationUnit ⊗[ℂ] DilationUnit :=
  (TensorProduct.mk ℂ DilationUnit DilationUnit).flip (EuclideanSpace.single 0 1)

@[simp] theorem unitDilation_apply (x : DilationUnit) :
    unitDilation x = x ⊗ₜ[ℂ] EuclideanSpace.single 0 1 := rfl

/-- The zero-copy dilation realizes the identity unit channel. -/
theorem dilationChannel_unitDilation : dilationChannel unitDilation = LinearMap.id := by
  have hslice : tensorRightSlice (EuclideanSpace.basisFun (Fin 1) ℂ) 0 ∘ₗ unitDilation =
      LinearMap.id := by
    ext x
    change tensorRightSlice (EuclideanSpace.basisFun (Fin 1) ℂ) 0
      (x ⊗ₜ[ℂ] EuclideanSpace.single 0 1) = x
    rw [tensorRightSlice_tmul]
    simp [EuclideanSpace.basisFun_toBasis]
  ext1 X
  rw [dilationChannel_kraus_basis (EuclideanSpace.basisFun (Fin 1) ℂ)]
  simp only [Fin.sum_univ_one, hslice]
  simp [krausTerm]

set_option backward.isDefEq.respectTransparency true in
theorem unitDilation_norm_le_one : ‖unitDilation.toContinuousLinearMap‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖x ⊗ₜ[ℂ] EuclideanSpace.single (0 : Fin 1) (1 : ℂ)‖ ≤ _
  simp [TensorProduct.norm_tmul, EuclideanSpace.norm_single]

variable {A B E : Type} [Qudit A] [Qudit B] [Qudit E]
  [Nontrivial A] [Nontrivial B] [Nontrivial E]

/-- The supplied dilation tensored `n` times in the canonical power spaces. -/
noncomputable def dilationPower (V : A →ₗ[ℂ] B ⊗[ℂ] E) :
    (n : ℕ) → TensorPower A n →ₗ[ℂ] TensorPower B n ⊗[ℂ] TensorPower E n
  | 0 => unitDilation
  | n + 1 => tensorDilation V (dilationPower V n)

/-- Exact identification with the concrete channel tensor powers. -/
theorem dilationChannel_dilationPower (N : CPTP A B) (V : A →ₗ[ℂ] B ⊗[ℂ] E)
    (hV : dilationChannel V = N.toLinearMap) (n : ℕ) :
    dilationChannel (dilationPower V n) = (channelPower N n).toLinearMap := by
  induction n with
  | zero => exact dilationChannel_unitDilation
  | succ n ih =>
    change dilationChannel (tensorDilation V (dilationPower V n)) =
      tensorSuperoperator N.toLinearMap (channelPower N n).toLinearMap
    rw [dilationChannel_tensorDilation, hV, ih]

/-- Tensor-word dilation, retaining its concrete shared environment. -/
noncomputable def wordDilation {ι : Type*} (U : ι → A →ₗ[ℂ] B ⊗[ℂ] E) :
    (n : ℕ) → (Fin n → ι) →
      TensorPower A n →ₗ[ℂ] TensorPower B n ⊗[ℂ] TensorPower E n
  | 0, _ => unitDilation
  | n + 1, word => tensorDilation (U (word 0)) (wordDilation U n (fun j => word j.succ))

/-- Summing all tensor words reconstructs the full tensor-power dilation. -/
theorem wordDilation_sum {ι : Type*} [Fintype ι]
    (U : ι → A →ₗ[ℂ] B ⊗[ℂ] E) (n : ℕ) :
    (∑ word : Fin n → ι, wordDilation U n word) = dilationPower (∑ i, U i) n := by
  classical
  induction n with
  | zero => simp [wordDilation, dilationPower]
  | succ n ih =>
    rw [← (Fin.consEquiv (fun _ : Fin (n+1) => ι)).sum_comp (wordDilation U (n+1)),
      Fintype.sum_prod_type]
    change (∑ i, ∑ word : Fin n → ι, tensorDilation (U i) (wordDilation U n word)) =
      tensorDilation (∑ i, U i) (dilationPower (∑ i, U i) n)
    calc
      _ = ∑ i, tensorDilation (U i) (∑ word : Fin n → ι, wordDilation U n word) := by
        apply Finset.sum_congr rfl
        intro i _
        exact (tensorDilation_sum_right (U i) (wordDilation U n)).symm
      _ = _ := by rw [ih, ← tensorDilation_sum_left]



/-- Product operator-norm bound, including the empty word. -/
theorem wordDilation_norm_le {ι : Type*} (U : ι → A →ₗ[ℂ] B ⊗[ℂ] E)
    (b : ι → ℝ) (hb : ∀ i, 0 ≤ b i)
    (hU : ∀ i, ‖(U i).toContinuousLinearMap‖ ≤ b i) (n : ℕ) (word : Fin n → ι) :
    ‖(wordDilation U n word).toContinuousLinearMap‖ ≤ ∏ j, b (word j) := by
  induction n with
  | zero => simpa [wordDilation] using unitDilation_norm_le_one
  | succ n ih =>
    rw [Fin.prod_univ_succ]
    exact (tensorDilation_norm_le _ _).trans
      (mul_le_mul (hU _) (ih _) (norm_nonneg (wordDilation U n (fun j => word j.succ)).toContinuousLinearMap) (hb _))

/-- Product CP-order bound against the actual channel power. -/
theorem wordDilation_cp_le {ι : Type*} (U : ι → A →ₗ[ℂ] B ⊗[ℂ] E)
    (M : CPTP A B) (lam : ι → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (hU : ∀ i, CPLe (dilationChannel (U i)) (lam i • M.toLinearMap))
    (n : ℕ) (word : Fin n → ι) :
    CPLe (dilationChannel (wordDilation U n word))
      ((∏ j, lam (word j)) • (channelPower M n).toLinearMap) := by
  induction n with
  | zero =>
    simp only [wordDilation, Fin.prod_univ_zero, one_smul]
    change CPLe (dilationChannel unitDilation) (LinearMap.id : T DilationUnit DilationUnit)
    rw [dilationChannel_unitDilation]
    change IsCompletelyPositive ((LinearMap.id : T DilationUnit DilationUnit) - LinearMap.id)
    rw [sub_self]
    simpa using cp_smul (cp_identity (C := DilationUnit)) (c := 0) le_rfl
  | succ n ih =>
    change CPLe (dilationChannel (tensorDilation (U (word 0))
      (wordDilation U n (fun j => word j.succ)))) _
    rw [dilationChannel_tensorDilation, Fin.prod_univ_succ]
    exact (hU _).tensor_scaled (ih _) (dilationChannel_cp _)
      ⟨(channelPower M n).toCompletelyPositiveMap, rfl⟩
      (Finset.prod_nonneg fun j _ => hlam _)

/-- The sum over tensor-word weights factors as the power of the one-block sum. -/
theorem word_weight_sum {ι : Type*} [Fintype ι] (b lam : ι → ℝ)
    (hb : ∀ i, 0 ≤ b i) (hlam : ∀ i, 0 ≤ lam i) (p : ℝ) (m : ℕ) :
    (∑ word : Fin m → ι, (∏ j, b (word j)) ^ (1 / p) *
      (∏ j, lam (word j)) ^ ((p - 1) / (2 * p))) =
      (∑ i, b i ^ (1 / p) * lam i ^ ((p - 1) / (2 * p))) ^ m := by
  classical
  have heq (word : Fin m → ι) :
      (∏ j, b (word j)) ^ (1 / p) * (∏ j, lam (word j)) ^ ((p - 1) / (2 * p)) =
      ∏ j, (b (word j) ^ (1 / p) * lam (word j) ^ ((p - 1) / (2 * p))) := by
    rw [← Real.finset_prod_rpow _ _ (fun j _ => hb (word j)),
      ← Real.finset_prod_rpow _ _ (fun j _ => hlam (word j)), Finset.prod_mul_distrib]
  simp_rw [heq]
  exact (Fintype.sum_pow (fun i => b i ^ (1 / p) * lam i ^ ((p - 1) / (2 * p))) m).symm



/-- Uniform linear bound in block length, proved using the actual tensor
powers and the concrete tensor-word construction. -/
theorem blockRenyi_dilation_rate_bound {ι : Type*} [Fintype ι]
    {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2)
    (N M : CPTP A B) (V : A →ₗ[ℂ] B ⊗[ℂ] E)
    (hV : dilationChannel V = N.toLinearMap)
    (U : ι → A →ₗ[ℂ] B ⊗[ℂ] E) (hVU : V = ∑ i, U i)
    (b lam : ι → ℝ) (hb : ∀ i, 0 ≤ b i) (hlam : ∀ i, 0 ≤ lam i)
    (hdom : ∀ i, CPLe (dilationChannel (U i)) (lam i • M.toLinearMap))
    (hnorm : ∀ i, ‖(U i).toContinuousLinearMap‖ ≤ b i) (m : ℕ) :
    blockRenyi p N M m ≤ ENNReal.ofReal ((m : ℝ) * ((2 * p / (p - 1)) *
      Real.logb 2 (∑ i, b i ^ (1 / p) * lam i ^ ((p - 1) / (2 * p))))) := by
  have h := channelRenyi_dilation_bound hp hp2 (channelPower N m) (channelPower M m)
    (dilationPower V m) (dilationChannel_dilationPower N V hV m)
    (wordDilation U m) (by rw [wordDilation_sum, ← hVU])
    (fun word => ∏ j, b (word j)) (fun word => ∏ j, lam (word j))
    (fun word => Finset.prod_nonneg fun j _ => hb (word j))
    (fun word => Finset.prod_nonneg fun j _ => hlam (word j))
    (wordDilation_cp_le U M lam hlam hdom m) (wordDilation_norm_le U b hb hnorm m)
  rw [word_weight_sum b lam hb hlam p m, Real.logb_pow] at h
  convert h using 1
  congr 1
  ring

/-- The complete finite-block filter/Schatten-to-regularization bridge. The
regularized quantity is the explicit block supremum from `Regularization`. -/
theorem regularizedRenyi_dilation_bound {ι : Type*} [Fintype ι]
    {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2)
    (N M : CPTP A B) (V : A →ₗ[ℂ] B ⊗[ℂ] E)
    (hV : dilationChannel V = N.toLinearMap)
    (U : ι → A →ₗ[ℂ] B ⊗[ℂ] E) (hVU : V = ∑ i, U i)
    (b lam : ι → ℝ) (hb : ∀ i, 0 ≤ b i) (hlam : ∀ i, 0 ≤ lam i)
    (hdom : ∀ i, CPLe (dilationChannel (U i)) (lam i • M.toLinearMap))
    (hnorm : ∀ i, ‖(U i).toContinuousLinearMap‖ ≤ b i) :
    regularizedRenyi p N M ≤ ENNReal.ofReal ((2 * p / (p - 1)) *
      Real.logb 2 (∑ i, b i ^ (1 / p) * lam i ^ ((p - 1) / (2 * p)))) := by
  apply iSup_le
  intro m
  apply iSup_le
  intro hm
  apply ENNReal.div_le_of_le_mul
  have h := blockRenyi_dilation_rate_bound hp hp2 N M V hV U hVU b lam hb hlam hdom hnorm m
  rw [ENNReal.ofReal_mul (Nat.cast_nonneg m)] at h
  simpa only [ENNReal.ofReal_natCast, mul_comm] using h

end QuantumChannelContinuity


