-- Prove2me | Definitions.Def_CRCD_QuantumChannelContinuity_StabilizedSchatten
-- name    : CRCD_QuantumChannelContinuity_StabilizedSchatten
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-08T03:20:36.812735+00:00
-- url     : https://prove2.me/theorems/78179ca4-0fa7-462a-9979-2b12b6617e34
-- title:
--   Reference amplification of a dilation
-- statement:
--   For $U:A\to B\otimes E$ and a reference space $R$, the canonical factor isometry sends $(B\otimes E)\otimes R$ to $(B\otimes R)\otimes E$. Define the stabilized dilation by
--   $$
--   \widetilde U=\mathrm{swap}_{E,R}\circ(U\otimes I_R).
--   $$
--   Its output channel is the original dilation channel amplified by the identity on $R$. The reference is retained and the same environment is traced out. The associated slice, sum, and norm identities transport the coefficient-based sandwiched Rényi estimates to stabilized channel outputs.
-- source:
--   https://github.com/JWang226/Continuity-of-regularized-channel-renyi-divergence/blob/e29274a69978bb499f00497481c6008befb0b84d/QuantumChannelContinuity/StabilizedSchatten.lean#L31-L167

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
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.LinearMapPiProd
import Mathlib.Topology.Algebra.Star.Unitary
import Definitions.Def_CRCD_QuantumChannelContinuity_Channels
import Definitions.Def_CRCD_QuantumChannelContinuity_Filter
import Definitions.Def_CRCD_QuantumChannelContinuity_FilterTensor
import Definitions.Def_CRCD_QuantumChannelContinuity_Foundations
import Definitions.Def_CRCD_QuantumChannelContinuity_Schatten
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
# The Schatten bound with an entangled reference

The reference amplification is implemented by tensoring each dilation with the
identity and moving the common environment to the final tensor factor. Partial
trace and complete-positive domination are proved to commute with this operation.
-/

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy
open scoped TensorProduct ComplexOrder

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false

namespace QuantumChannelContinuity

universe u
variable {A B E R : Type u} [Qudit A] [Qudit B] [Qudit E] [Qudit R]

/-- The canonical isometry that moves the environment past a reference. -/
noncomputable def referenceSwap : (B ⊗[ℂ] E) ⊗[ℂ] R ≃ₗᵢ[ℂ] (B ⊗[ℂ] R) ⊗[ℂ] E :=
  (TensorProduct.assocIsometry ℂ B E R).trans
    ((TensorProduct.congrIsometry (LinearIsometryEquiv.refl ℂ B)
      (TensorProduct.commIsometry ℂ E R)).trans
      (TensorProduct.assocIsometry ℂ B R E).symm)

@[simp] theorem referenceSwap_tmul (b : B) (e : E) (r : R) :
    referenceSwap ((b ⊗ₜ[ℂ] e) ⊗ₜ[ℂ] r) = (b ⊗ₜ[ℂ] r) ⊗ₜ[ℂ] e := by
  simp [referenceSwap]

/-- Dilation of the channel amplified by the identity on the reference. -/
noncomputable def stabilizedDilation (U : A →ₗ[ℂ] B ⊗[ℂ] E) :
    A ⊗[ℂ] R →ₗ[ℂ] (B ⊗[ℂ] R) ⊗[ℂ] E :=
  referenceSwap.toLinearMap ∘ₗ TensorProduct.map U LinearMap.id

/-- Dilation decompositions survive reference amplification in a common environment. -/
theorem stabilizedDilation_sum {ι : Type*} [Fintype ι]
    (U : ι → A →ₗ[ℂ] B ⊗[ℂ] E) :
    stabilizedDilation (R := R) (∑ i, U i) = ∑ i, stabilizedDilation (R := R) (U i) := by
  ext a r
  simp [stabilizedDilation, TensorProduct.sum_tmul]

/-- Environmental slices commute with the reference-factor permutation. -/
theorem slice_referenceSwap (j : Fin (Module.finrank ℂ E)) (x : B ⊗[ℂ] E) (r : R) :
    tensorRightSlice (stdOrthonormalBasis ℂ E) j (referenceSwap (x ⊗ₜ[ℂ] r)) =
      tensorRightSlice (stdOrthonormalBasis ℂ E) j x ⊗ₜ[ℂ] r := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b e => simp [tensorRightSlice_tmul, TensorProduct.smul_tmul']
  | add x y hx hy => simp_all [TensorProduct.add_tmul]

/-- Kraus operators of the amplified dilation are the original Kraus operators
with an identity reference factor. -/
theorem stabilizedDilation_slice (U : A →ₗ[ℂ] B ⊗[ℂ] E)
    (j : Fin (Module.finrank ℂ E)) :
    tensorRightSlice (stdOrthonormalBasis ℂ E) j ∘ₗ stabilizedDilation (R := R) U =
      TensorProduct.map (tensorRightSlice (stdOrthonormalBasis ℂ E) j ∘ₗ U)
        (LinearMap.id : R →ₗ[ℂ] R) := by
  ext a r
  simp [stabilizedDilation, slice_referenceSwap]

/-- Exact Kraus expansion of the partial trace of an arbitrary supplied dilation. -/
theorem dilationChannel_kraus_sum (U : A →ₗ[ℂ] B ⊗[ℂ] E) (X : L A) :
    dilationChannel U X = ∑ j : Fin (Module.finrank ℂ E),
      krausTerm (tensorRightSlice (stdOrthonormalBasis ℂ E) j ∘ₗ U) X := by
  unfold dilationChannel
  rw [LinearMap.comp_apply, TrRight_eq_kraus_sum (stdOrthonormalBasis ℂ E)]
  apply Finset.sum_congr rfl
  intro j _
  simp [krausTerm, LinearMap.adjoint_comp, LinearMap.comp_assoc]

/-- Reference amplification of the actual dilation equals the tensor product of
its actual channel with the identity superoperator, on every input operator. -/
theorem dilationChannel_stabilized (U : A →ₗ[ℂ] B ⊗[ℂ] E) :
    dilationChannel (stabilizedDilation (R := R) U) =
      tensorSuperoperator (dilationChannel U) (LinearMap.id : T R R) := by
  apply LinearMap.ext
  intro Z
  obtain ⟨z, rfl⟩ := (l_tensor_equiv (ℋ₁ := A) (ℋ₂ := R)).symm.surjective Z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul X Y =>
    rw [l_tensor_equiv_symm_tmul, tensorSuperoperator_apply,
      dilationChannel_kraus_sum, dilationChannel_kraus_sum]
    simp_rw [stabilizedDilation_slice, tensor_kraus_apply]
    ext a r
    simp [krausTerm, TensorProduct.sum_tmul]
  | add x y hx hy => simp_all

/-- Appending an identity reference and permuting tensor factors does not
increase the dilation's operator norm. -/
theorem stabilizedDilation_norm_le (U : A →ₗ[ℂ] B ⊗[ℂ] E) :
    ‖(stabilizedDilation (R := R) U).toContinuousLinearMap‖ ≤
      ‖U.toContinuousLinearMap‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg U.toContinuousLinearMap)
  intro ψ
  change ‖referenceSwap (TensorProduct.map U (LinearMap.id : L R) ψ)‖ ≤ _
  rw [referenceSwap.norm_map]
  calc
    ‖TensorProduct.map U (LinearMap.id : L R) ψ‖ ≤
        ‖(TensorProduct.map U (LinearMap.id : L R)).toContinuousLinearMap‖ * ‖ψ‖ :=
      (TensorProduct.map U (LinearMap.id : L R)).toContinuousLinearMap.le_opNorm ψ
    _ ≤ ‖U.toContinuousLinearMap‖ * ‖ψ‖ :=
      mul_le_mul_of_nonneg_right (tensorMap_left_norm_le (E := R) U) (norm_nonneg ψ)

/-- The complete one-shot Stinespring/Schatten estimate, uniformly over every
finite reference space and every possibly entangled pure input. All component
bounds are the original, unamplified CP-order and operator-norm bounds. -/
theorem stabilized_channel_dilation_schatten_bound {ι : Type*} [Fintype ι]
    {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) (N M : CPTP A B)
    (V : A →ₗ[ℂ] B ⊗[ℂ] E) (hV : dilationChannel V = N.toLinearMap)
    (U : ι → A →ₗ[ℂ] B ⊗[ℂ] E) (hVU : V = ∑ i, U i)
    (b lam : ι → ℝ) (hb : ∀ i, 0 ≤ b i) (hlam : ∀ i, 0 ≤ lam i)
    (hdom : ∀ i, CPLe (dilationChannel (U i)) (lam i • M.toLinearMap))
    (hnorm : ∀ i, ‖(U i).toContinuousLinearMap‖ ≤ b i)
    (ψ : A ⊗[ℂ] R) (hψ : ‖ψ‖ = 1) :
    (sandwichedQuasi p
      (tensorSuperoperator N.toLinearMap (LinearMap.id : T R R) (outer_product ψ ψ))
      (tensorSuperoperator M.toLinearMap (LinearMap.id : T R R) (outer_product ψ ψ))).re ^
        (1 / (2 * p)) ≤
      ∑ i, b i ^ (1 / p) * lam i ^ ((p - 1) / (2 * p)) := by
  let ρ := outer_product ψ ψ
  let σ := tensorSuperoperator M.toLinearMap (LinearMap.id : T R R) ρ
  have hρ : 0 ≤ ρ := outer_product_self_nonneg ψ
  have hM : IsCompletelyPositive M.toLinearMap := ⟨M.toCompletelyPositiveMap, rfl⟩
  have hσ : σ.IsPositive := (LinearMap.nonneg_iff_isPositive _).1
    (completelyPositive_to_positiveMap _ (tensorSuperoperator_cp _ _ hM cp_identity) ρ hρ)
  have hdomR (i : ι) :
      TrRight (krausTerm (stabilizedDilation (R := R) (U i)) ρ) ≤ lam i • σ := by
    change dilationChannel (stabilizedDilation (R := R) (U i)) ρ ≤ _
    rw [dilationChannel_stabilized]
    have h := ((hdom i).tensor_identity_scaled (C := R) (dilationChannel_cp (U i))).apply_nonneg hρ
    simpa only [LinearMap.smul_apply] using h
  have h := sandwichedQuasi_dilation_bound hp hp2 σ hσ
    (fun i => stabilizedDilation (R := R) (U i)) ψ hψ b lam hb hlam hdomR
    (fun i => (stabilizedDilation_norm_le (R := R) (U i)).trans (hnorm i))
  rw [← stabilizedDilation_sum, ← hVU] at h
  change (sandwichedQuasi p (dilationChannel (stabilizedDilation (R := R) V) ρ) σ).re ^
    (1 / (2 * p)) ≤ _ at h
  rw [dilationChannel_stabilized, hV] at h
  exact h

/-- The same estimate in the upstream `amplifyWithId` convention used by the
project's stabilized channel divergence. -/
theorem amplify_channel_dilation_schatten_bound {ι : Type*} [Fintype ι]
    {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) (N M : CPTP A B)
    (V : A →ₗ[ℂ] B ⊗[ℂ] E) (hV : dilationChannel V = N.toLinearMap)
    (U : ι → A →ₗ[ℂ] B ⊗[ℂ] E) (hVU : V = ∑ i, U i)
    (b lam : ι → ℝ) (hb : ∀ i, 0 ≤ b i) (hlam : ∀ i, 0 ≤ lam i)
    (hdom : ∀ i, CPLe (dilationChannel (U i)) (lam i • M.toLinearMap))
    (hnorm : ∀ i, ‖(U i).toContinuousLinearMap‖ ≤ b i)
    (ψ : A ⊗[ℂ] A) (hψ : ‖ψ‖ = 1) :
    (sandwichedQuasi p (amplifyWithId N.toLinearMap (outer_product ψ ψ))
      (amplifyWithId M.toLinearMap (outer_product ψ ψ))).re ^ (1 / (2 * p)) ≤
      ∑ i, b i ^ (1 / p) * lam i ^ ((p - 1) / (2 * p)) :=
  stabilized_channel_dilation_schatten_bound hp hp2 N M V hV U hVU b lam hb hlam hdom hnorm ψ hψ

end QuantumChannelContinuity


