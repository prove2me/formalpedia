-- Prove2me | Definitions.Def_CRCD_QuantumChannelContinuity_SlackTester
-- name    : CRCD_QuantumChannelContinuity_SlackTester
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-08T03:20:07.297666+00:00
-- url     : https://prove2.me/theorems/582f9907-b20e-498b-80ef-a29e10e38537
-- title:
--   Choi tester factorization and hockey-stick upper bounds
-- statement:
--   For finite-dimensional complex Hilbert spaces with nonzero input/output, use Choi operators $J(\Phi)$ on $B\otimes A$ and the unnormalized reference vector $\Omega_A\in A\otimes A$. If $0\le W\le I_B\otimes Y$ with $Y\ge0$, then there is an effect $0\le T\le I$ such that
--
--   $$
--   W=(I_B\otimes\sqrt Y)^\dagger T(I_B\otimes\sqrt Y).
--   $$
--
--   For CPTP $N,M$ and $\gamma\ge0$,
--
--   $$
--   \operatorname{Re}\operatorname{Tr}[W(J(N)-\gamma J(M))]\le\delta_\gamma(N,M)\operatorname{Re}\operatorname{Tr}Y;
--   $$
--
--   when $\operatorname{Re}\operatorname{Tr}Y=1$, the right side is exactly $\delta_\gamma(N,M)$.
--
--   Every vector in $A\otimes A$ equals $(I_A\otimes R)\Omega_A$ for some operator $R$ on $A$, with squared norm $\operatorname{Re}\operatorname{Tr}(R^\dagger R)$. Its amplified output under $\Phi\otimes\mathrm{id}$ is $(I_B\otimes R)J(\Phi)(I_B\otimes R)^\dagger$. Reference-side conjugation commutes with amplification. The supplied cyclic-trace identity retains the order $W=K^\dagger TK\Rightarrow\operatorname{Tr}(WX)=\operatorname{Tr}(TKXK^\dagger)$, for an operator $K$ on $B\otimes A$, and the square-root Gram identity is $(I_B\otimes\sqrt Y)^\dagger(I_B\otimes\sqrt Y)=I_B\otimes Y$.
-- source:
--   https://github.com/JWang226/Continuity-of-regularized-channel-renyi-divergence/blob/e29274a69978bb499f00497481c6008befb0b84d/QuantumChannelContinuity/SlackTester.lean#L24-L191

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
import Mathlib.Analysis.Convex.Cone.Dual
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
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
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
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
import Definitions.Def_CRCD_QuantumChannelContinuity_ChoiSupport
import Definitions.Def_CRCD_QuantumChannelContinuity_Filter
import Definitions.Def_CRCD_QuantumChannelContinuity_FilterAlignment
import Definitions.Def_CRCD_QuantumChannelContinuity_FilterSlack
import Definitions.Def_CRCD_QuantumChannelContinuity_Foundations
import Definitions.Def_CRCD_QuantumChannelContinuity_HockeyStick
import Definitions.Def_CRCD_QuantumChannelContinuity_SDPTrace
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





/-! # Choi dual effects as physical channel tests -/

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy
open scoped ComplexOrder TensorProduct

namespace QuantumChannelContinuity

universe u
variable {A B R : Type u} [Qudit A] [Qudit B] [Qudit R]
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false

/-- A reference operation commutes exactly with channel amplification. -/
theorem tensorSuperoperator_reference_kraus (Φ : T A B) (S : L R)
    (X : L (A ⊗[ℂ] R)) :
    tensorSuperoperator Φ (LinearMap.id : T R R)
        (krausTerm (environmentMap (B := A) S) X) =
      krausTerm (environmentMap (B := B) S)
        (tensorSuperoperator Φ (LinearMap.id : T R R) X) := by
  obtain ⟨x,rfl⟩ := (l_tensor_equiv (ℋ₁ := A) (ℋ₂ := R)).symm.surjective X
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul U V =>
    rw [l_tensor_equiv_symm_tmul]
    simp only [environmentMap]
    rw [tensor_kraus_apply,tensorSuperoperator_apply,tensorSuperoperator_apply,tensor_kraus_apply]
    simp [krausTerm]
  | add x y hx hy => simp_all

/-- Applying the reference map to the Choi vector gives a purification whose
squared norm is exactly the Gram trace of the reference map. -/
theorem norm_reference_choiVector_sq (S : L A) :
    ‖environmentMap (B := A) S (choiVector A)‖ ^ 2 =
      (Tr ((LinearMap.adjoint S).comp S)).re := by
  have hv : environmentMap (B := A) S (choiVector A) =
      TensorProduct.comm ℂ A A (vec (stdOrthonormalBasis ℂ A).toBasis S) := by
    simp [choiVector,vec_apply,environmentMap]
  rw [hv,TensorProduct.norm_comm]
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ),inner_vec_eq_trace]
  rfl

/-- An actual pure-input output is a weighted Choi operator. -/
theorem amplify_weighted_choi (Φ : T A B) (S : L A) :
    amplifyWithId Φ
      (outer_product (environmentMap (B := A) S (choiVector A))
        (environmentMap (B := A) S (choiVector A))) =
      krausTerm (environmentMap (B := B) S) (choi (stdOrthonormalBasis ℂ A).toBasis Φ) := by
  rw [← comp_outer_product_adjoint]
  change tensorSuperoperator Φ (LinearMap.id : T A A)
      (krausTerm (environmentMap (B := A) S) (outer_product (choiVector A) (choiVector A))) = _
  rw [tensorSuperoperator_reference_kraus]
  rfl

/-- The reference square-root map has exactly the prescribed Gram operator. -/
theorem environment_sqrt_gram (Y : L A) (hY : 0 ≤ Y) :
    (LinearMap.adjoint (environmentMap (B := B) (CFC.sqrt Y))).comp
        (environmentMap (B := B) (CFC.sqrt Y)) = environmentMap (B := B) Y := by
  simp only [environmentMap,TensorProduct.adjoint_map,← TensorProduct.map_comp,
    LinearMap.adjoint_id,LinearMap.id_comp]
  congr 1
  change star (CFC.sqrt Y) * CFC.sqrt Y = Y
  rw [(CFC.sqrt_nonneg Y).isSelfAdjoint.star_eq]
  exact CFC.sqrt_mul_sqrt_self Y hY

/-- Every operator below an identity-tensored positive operator is a physical
effect in the corresponding purification, even if the reference is singular. -/
theorem exists_choi_effect (W : L (B ⊗[ℂ] A)) (Y : L A)
    (hW : 0 ≤ W) (hY : 0 ≤ Y) (hle : W ≤ environmentMap (B := B) Y) :
    ∃ T : Effect (B ⊗[ℂ] A), W =
      (LinearMap.adjoint (environmentMap (B := B) (CFC.sqrt Y))).comp
        (T.op.comp (environmentMap (B := B) (CFC.sqrt Y))) := by
  let S := environmentMap (B := B) (CFC.sqrt Y)
  have hWgram : (LinearMap.adjoint (CFC.sqrt W)).comp (CFC.sqrt W) = W := by
    change star (CFC.sqrt W) * CFC.sqrt W = W
    rw [(CFC.sqrt_nonneg W).isSelfAdjoint.star_eq]
    exact CFC.sqrt_mul_sqrt_self W hW
  obtain ⟨U,hU,hUS⟩ := exists_contraction_factor_of_gram_le (CFC.sqrt W) S (by
    rw [hWgram,environment_sqrt_gram Y hY]
    exact hle)
  let T : Effect (B ⊗[ℂ] A) := ⟨(LinearMap.adjoint U).comp U,
    by change 0 ≤ star U * U; exact star_mul_self_nonneg U,hU⟩
  refine ⟨T,?_⟩
  rw [← hWgram,hUS,LinearMap.adjoint_comp]
  simp only [T,LinearMap.comp_assoc]
  rfl

/-- The dual Choi objective is the acceptance difference of the resulting test. -/
theorem trace_choi_effect (W : L (B ⊗[ℂ] A)) (S : L (B ⊗[ℂ] A))
    (T : Effect (B ⊗[ℂ] A)) (hW : W = (LinearMap.adjoint S).comp (T.op.comp S))
    (X : L (B ⊗[ℂ] A)) : Tr (W * X) = Tr (T.op * krausTerm S X) := by
  rw [hW]
  change Tr ((LinearMap.adjoint S).comp ((T.op.comp S).comp X)) =
    Tr (T.op.comp (S.comp (X.comp (LinearMap.adjoint S))))
  rw [LinearMap.trace_comp_comm']
  simp only [LinearMap.comp_assoc]

variable [Nontrivial A] [Nontrivial B]

/-- A normalized feasible Choi dual pair is a genuine pure-input channel test. -/
theorem normalized_choi_test_le_hockey (N M : CPTP A B) {γ : ℝ} (hγ : 0 ≤ γ)
    (W : L (B ⊗[ℂ] A)) (Y : L A) (hW : 0 ≤ W) (hY : 0 ≤ Y)
    (hle : W ≤ environmentMap (B := B) Y) (htr : (Tr Y).re = 1) :
    (Tr (W * (choi (stdOrthonormalBasis ℂ A).toBasis N.toLinearMap -
      (γ : ℂ) • choi (stdOrthonormalBasis ℂ A).toBasis M.toLinearMap))).re ≤
      channelHockey γ N M := by
  have hgram : (LinearMap.adjoint (CFC.sqrt Y)).comp (CFC.sqrt Y) = Y := by
    change star (CFC.sqrt Y) * CFC.sqrt Y = Y
    rw [(CFC.sqrt_nonneg Y).isSelfAdjoint.star_eq]
    exact CFC.sqrt_mul_sqrt_self Y hY
  have hnorm : ‖environmentMap (B := A) (CFC.sqrt Y) (choiVector A)‖ = 1 := by
    have h := norm_reference_choiVector_sq (CFC.sqrt Y)
    rw [hgram,htr] at h
    nlinarith [norm_nonneg (environmentMap (B := A) (CFC.sqrt Y) (choiVector A))]
  let ψ : PureInput (A ⊗[ℂ] A) := ⟨environmentMap (B := A) (CFC.sqrt Y) (choiVector A),hnorm⟩
  obtain ⟨T,hT⟩ := exists_choi_effect W Y hW hY hle
  have hprob (Φ : CPTP A B) :
      (Tr (W * choi (stdOrthonormalBasis ℂ A).toBasis Φ.toLinearMap)).re =
        T.probability (amplifiedOutput Φ ψ.density) := by
    rw [trace_choi_effect W (environmentMap (B := B) (CFC.sqrt Y)) T hT]
    rw [← amplify_weighted_choi]
    rfl
  have hobj :
      (Tr (W * (choi (stdOrthonormalBasis ℂ A).toBasis N.toLinearMap -
        (γ : ℂ) • choi (stdOrthonormalBasis ℂ A).toBasis M.toLinearMap))).re =
      T.probability (amplifiedOutput N ψ.density) - γ *
        T.probability (amplifiedOutput M ψ.density) := by
    simp only [mul_sub,map_sub,Complex.sub_re,mul_smul_comm,map_smul,smul_eq_mul,
      Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,hprob]
  rw [hobj]
  apply le_trans (le_csSup (s := Set.range (fun T : Effect (B ⊗[ℂ] A) =>
    T.probability (amplifiedOutput N ψ.density) - γ * T.probability (amplifiedOutput M ψ.density)))
    ⟨1, by rintro _ ⟨T,rfl⟩; exact hockey_objective_le_one hγ _ _ T⟩ (Set.mem_range_self T))
  apply le_csSup (s := Set.range (fun φ : PureInput (A ⊗[ℂ] A) =>
    stateHockey γ (amplifiedOutput N φ.density) (amplifiedOutput M φ.density)))
    ⟨1, by rintro _ ⟨φ,rfl⟩; exact stateHockey_le_one hγ _ _⟩ (Set.mem_range_self ψ)

/-- Every bipartite vector arises by applying a reference operator to the Choi vector. -/
theorem reference_choiVector_surjective :
    Function.Surjective (fun S : L A => environmentMap (B := A) S (choiVector A)) := by
  intro ψ
  obtain ⟨S,hS⟩ := (vecLinearEquiv (stdOrthonormalBasis ℂ A).toBasis).surjective
    (TensorProduct.comm ℂ A A ψ)
  refine ⟨S,?_⟩
  have hv : environmentMap (B := A) S (choiVector A) =
      TensorProduct.comm ℂ A A (vec (stdOrthonormalBasis ℂ A).toBasis S) := by
    simp [choiVector,vec_apply,environmentMap]
  change environmentMap (B := A) S (choiVector A) = ψ
  rw [hv,show vec (stdOrthonormalBasis ℂ A).toBasis S = TensorProduct.comm ℂ A A ψ from hS]
  simp

/-- Every feasible, possibly unnormalized Choi dual pair is bounded by the
actual stabilized channel hockey-stick divergence times its normalization. -/
theorem choi_test_le_hockey (N M : CPTP A B) {γ : ℝ} (hγ : 0 ≤ γ)
    (W : L (B ⊗[ℂ] A)) (Y : L A) (hW : 0 ≤ W) (hY : 0 ≤ Y)
    (hle : W ≤ environmentMap (B := B) Y) :
    (Tr (W * (choi (stdOrthonormalBasis ℂ A).toBasis N.toLinearMap -
      (γ : ℂ) • choi (stdOrthonormalBasis ℂ A).toBasis M.toLinearMap))).re ≤
      channelHockey γ N M * (Tr Y).re := by
  by_cases hY0 : Y = 0
  · have hW0 : W = 0 := le_antisymm (by simpa [hY0,environmentMap] using hle) hW
    simp [hY0,hW0]
  have hc : 0 < (Tr Y).re := trace_re_pos_of_ne_zero hY hY0
  let c := (Tr Y).re
  have hcn : (0 : ℂ) ≤ (c⁻¹ : ℝ) := by exact_mod_cast (inv_nonneg.mpr hc.le)
  let W' := ((c⁻¹ : ℝ) : ℂ) • W
  let Y' := ((c⁻¹ : ℝ) : ℂ) • Y
  have hle' : W' ≤ environmentMap (B := B) Y' := by
    have heq : environmentMap (B := B) Y' = ((c⁻¹ : ℝ) : ℂ) • environmentMap (B := B) Y := by
      exact TensorProduct.map_smul_right _ _ _
    rw [heq]
    exact smul_le_smul_of_nonneg_left hle hcn
  have htr : (Tr Y').re = 1 := by
    simp [Y',c,Complex.mul_re,hc.ne']
  have h := normalized_choi_test_le_hockey N M hγ W' Y'
    (smul_nonneg hcn hW) (smul_nonneg hcn hY) hle' htr
  have heq (X : L (B ⊗[ℂ] A)) :
      (Tr (W' * X)).re = c⁻¹ * (Tr (W * X)).re := by
    simp [W',Complex.mul_re]
  rw [heq] at h
  simpa only [mul_comm] using (inv_mul_le_iff₀ hc).mp h

end QuantumChannelContinuity


