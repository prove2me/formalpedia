-- Prove2me | Definitions.Def_CRCD_QuantumChannelContinuity_FilterSlack
-- name    : CRCD_QuantumChannelContinuity_FilterSlack
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-08T00:05:00.274635+00:00
-- url     : https://prove2.me/theorems/9b15157d-185a-4328-8ab1-337abb972bac
-- title:
--   Orthogonal environmental sums of dilations
-- statement:
--   Give $E\oplus F$ its Hilbert direct-sum norm and canonical isometric inclusions $\iota_E,\iota_F$. For dilations $V:A\to B\otimes E$ and $W:A\to B\otimes F$, define
--   $$
--   V\boxplus W=(I_B\otimes\iota_E)V+(I_B\otimes\iota_F)W.
--   $$
--   The two environmental sectors are orthogonal. Consequently, tracing out the environment gives $\Phi_{V\boxplus W}=\Phi_V+\Phi_W$, with no cross terms. These constructions support completely positive slack filtering and convert trace bounds on pure inputs into norm bounds for the associated dilation.
-- source:
--   https://github.com/JWang226/Continuity-of-regularized-channel-renyi-divergence/blob/e29274a69978bb499f00497481c6008befb0b84d/QuantumChannelContinuity/FilterSlack.lean#L29-L188

import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Trace
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Algebra.Module.LinearMapPiProd
import Definitions.Def_CRCD_QuantumChannelContinuity_Filter
import Definitions.Def_CRCD_QuantumChannelContinuity_FilterAlignment
import Definitions.Def_CRCD_Quantum_QuantumMechanics_QuantumChannel_part_4
import Definitions.Def_CRCD_Quantum_QuantumMechanics_QuantumState

/-
Copyright (c) 2026 Jinzhao Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzhao Wang (AI-assisted formalization)
-/




/-!
# Filtering from a completely positive slack map

This file supplies the direct-sum and ordered-dilation construction underlying
Gour's filter.  Its explicit input is a positive slack map dominating the
channel difference, together with an operator-norm bound for its dilation.
The optimized value of that slack bound is the separate SDP-duality question.
-/

open QuantumState QuantumChannel TensorProduct
open scoped ComplexOrder BigOperators

namespace QuantumChannelContinuity

universe u
variable {A B E F G : Type u} [Qudit A] [Qudit B] [Qudit E] [Qudit F] [Qudit G]

set_option maxHeartbeats 800000

noncomputable instance sumEnvironmentQudit : Qudit (WithLp 2 (E × F)) where
  toNormedAddCommGroup := inferInstance
  toInnerProductSpace := inferInstance
  toCompleteSpace := inferInstance
  fg_top := Module.Finite.fg_top

noncomputable def environmentInl : E →ₗ[ℂ] WithLp 2 (E × F) :=
  (WithLp.linearEquiv 2 ℂ (E × F)).symm.toLinearMap.comp (LinearMap.inl ℂ E F)

noncomputable def environmentInr : F →ₗ[ℂ] WithLp 2 (E × F) :=
  (WithLp.linearEquiv 2 ℂ (E × F)).symm.toLinearMap.comp (LinearMap.inr ℂ E F)

theorem environmentInl_isometry :
    (LinearMap.adjoint (environmentInl (E := E) (F := F))).comp environmentInl = 1 := by
  ext1 x
  apply ext_inner_right ℂ
  intro y
  simp [LinearMap.adjoint_inner_left, environmentInl, WithLp.prod_inner_apply]

theorem environmentInr_isometry :
    (LinearMap.adjoint (environmentInr (E := E) (F := F))).comp environmentInr = 1 := by
  ext1 x
  apply ext_inner_right ℂ
  intro y
  simp [LinearMap.adjoint_inner_left, environmentInr, WithLp.prod_inner_apply]

theorem dilationChannel_environment_isometry
    (U : E →ₗ[ℂ] F) (V : A →ₗ[ℂ] B ⊗[ℂ] E)
    (hU : (LinearMap.adjoint U).comp U = 1) :
    dilationChannel ((environmentMap (B := B) U).comp V) = dilationChannel V := by
  have h := environment_defect_identity (B := B) U (0 : L E) (by simpa using hU)
  have hzero : (TrRight (ℋ₂ := B) (ℋ₃ := E)).comp
      (krausTerm (environmentMap (B := B) (0 : L E))) = 0 := by
    ext1 X
    simp [environmentMap, krausTerm]
  rw [hzero] at h
  have heq := sub_eq_zero.mp h
  unfold dilationChannel
  rw [krausTerm_comp, ← LinearMap.comp_assoc, ← heq]

/-- Put two supplied dilation operators in orthogonal environmental sectors. -/
noncomputable def directSumDilation
    (V : A →ₗ[ℂ] B ⊗[ℂ] E) (W : A →ₗ[ℂ] B ⊗[ℂ] F) :
    A →ₗ[ℂ] B ⊗[ℂ] WithLp 2 (E × F) :=
  (environmentMap (B := B) environmentInl).comp V +
    (environmentMap (B := B) environmentInr).comp W

theorem directSumDilation_channel
    (V : A →ₗ[ℂ] B ⊗[ℂ] E) (W : A →ₗ[ℂ] B ⊗[ℂ] F) :
    dilationChannel (directSumDilation V W) = dilationChannel V + dilationChannel W := by
  have houter (a c : A) :
      dilationChannel (directSumDilation V W) (outer_product a c) =
        dilationChannel V (outer_product a c) + dilationChannel W (outer_product a c) := by
    simp only [dilationChannel_outer_product]
    ext1 x
    apply ext_inner_left ℂ
    intro y
    simp only [LinearMap.add_apply, inner_add_right, ← inner_outputSlice]
    simp [directSumDilation, outputSlice_environmentMap, environmentInl, environmentInr,
      WithLp.prod_inner_apply]
  ext1 X
  rw [linearMap_eq_sum_outer_product (stdOrthonormalBasis ℂ A) X]
  simp only [map_sum, LinearMap.add_apply, houter, Finset.sum_add_distrib]

theorem environment_dilation_norm_le
    (U : E →ₗ[ℂ] F) (V : A →ₗ[ℂ] B ⊗[ℂ] E)
    (hU : (LinearMap.adjoint U).comp U ≤ 1) :
    ‖((environmentMap (B := B) U).comp V).toContinuousLinearMap‖ ≤
      ‖V.toContinuousLinearMap‖ := by
  have h := fixed_environment_error U ((environmentMap (B := B) U).comp V)
    0 V hU (by simp)
  simpa only [LinearMap.comp_zero, sub_zero] using h

/-- A completely positive slack dominator gives a filter in the *prescribed*
dilation, with error no larger than the slack dilation's operator norm.
This proves the operator construction of Gour equations (46)–(49) and the
fixed-environment transfer in a single theorem. -/
theorem filter_of_slack_dilation
    (V : A →ₗ[ℂ] B ⊗[ℂ] E) (M : A →ₗ[ℂ] B ⊗[ℂ] F)
    (Q : A →ₗ[ℂ] B ⊗[ℂ] G)
    (hV : CPLe (dilationChannel V) (dilationChannel M + dilationChannel Q)) :
    ∃ W : A →ₗ[ℂ] B ⊗[ℂ] E,
      CPLe (dilationChannel W) (dilationChannel M) ∧
      ‖(V - W).toContinuousLinearMap‖ ≤ ‖Q.toContinuousLinearMap‖ := by
  obtain ⟨U, hU, hUV⟩ := exists_ordered_dilation_factor V (directSumDilation M Q)
    (by simpa only [directSumDilation_channel] using hV)
  let X := (environmentMap (B := B) (environmentInl (E := F) (F := G))).comp M
  let Y := (environmentMap (B := B) (environmentInr (E := F) (F := G))).comp Q
  have hX : dilationChannel X = dilationChannel M :=
    dilationChannel_environment_isometry _ _ environmentInl_isometry
  have hY : ‖Y.toContinuousLinearMap‖ ≤ ‖Q.toContinuousLinearMap‖ :=
    environment_dilation_norm_le _ _ environmentInr_isometry.le
  refine ⟨(environmentMap (B := B) U).comp X, ?_, ?_⟩
  · simpa only [hX] using dilationChannel_environment_le U X hU
  · exact (fixed_environment_error U V X Y hU hUV).trans hY

/-- The concrete partial trace preserves the scalar trace. -/
theorem trace_trRight (X : L (B ⊗[ℂ] E)) : Tr (TrRight X) = Tr X := by
  obtain ⟨x, rfl⟩ := (l_tensor_equiv (ℋ₁ := B) (ℋ₂ := E)).symm.surjective X
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul X Y =>
    rw [l_tensor_equiv_symm_tmul, trRight_map]
    simpa only [map_smul, smul_eq_mul, Tr, LinearMap.trace_tensorProduct'] using
      mul_comm (Tr Y) (Tr X)
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

/-- The trace of a pure-input channel output is exactly the squared norm
of the dilation applied to that input. -/
theorem trace_dilationChannel_outer_self
    (Q : A →ₗ[ℂ] B ⊗[ℂ] E) (a : A) :
    (Tr (dilationChannel Q (outer_product a a))).re = ‖Q a‖ ^ 2 := by
  rw [dilationChannel_outer_product, trace_trRight, trace_outer_product]
  exact inner_self_eq_norm_sq (𝕜 := ℂ) _

/-- A trace bound for a CP map bounds the operator norm of every supplied
Stinespring dilation, with no support or invertibility assumptions. -/
theorem dilation_norm_le_sqrt_of_trace_bound
    (Q : A →ₗ[ℂ] B ⊗[ℂ] E) (ε : ℝ) (hε : 0 ≤ ε)
    (hQ : ∀ a : A, (Tr (dilationChannel Q (outer_product a a))).re ≤ ε * ‖a‖ ^ 2) :
    ‖Q.toContinuousLinearMap‖ ≤ Real.sqrt ε := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg ε)
  intro a
  have h := hQ a
  rw [trace_dilationChannel_outer_self] at h
  have hs := Real.sq_sqrt hε
  have hn : 0 ≤ Real.sqrt ε * ‖a‖ := mul_nonneg (Real.sqrt_nonneg ε) (norm_nonneg a)
  have hsq : (Real.sqrt ε * ‖a‖) ^ 2 = ε * ‖a‖ ^ 2 := by rw [mul_pow, hs]
  change ‖Q a‖ ≤ Real.sqrt ε * ‖a‖
  nlinarith [norm_nonneg (Q a)]

/-- The entire filter construction, conditional only on a CP slack map with
the displayed trace bound.  The missing optimized assertion is exactly the
existence of such a `Q` with `ε = E_λ(N‖M)` (Gour equation (44)). -/
theorem fixed_dilation_filter_of_cp_slack
    (V : A →ₗ[ℂ] B ⊗[ℂ] E) (Λ Q : QuantumChannel.T A B)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hΛ : IsCompletelyPositive Λ) (hQ : IsCompletelyPositive Q)
    (hdom : CPLe (dilationChannel V) (Λ + Q))
    (htrace : ∀ a : A, (Tr (Q (outer_product a a))).re ≤ ε * ‖a‖ ^ 2) :
    ∃ W : A →ₗ[ℂ] B ⊗[ℂ] E,
      CPLe (dilationChannel W) Λ ∧
      ‖(V - W).toContinuousLinearMap‖ ≤ Real.sqrt ε := by
  let a := stdOrthonormalBasis ℂ A
  obtain ⟨F, instF, hM⟩ := cp_to_stinespring a.toBasis Λ hΛ
  letI := instF
  obtain ⟨M, hM⟩ := hM
  have hM' : dilationChannel M = Λ := by
    ext1 X
    exact (hM X).symm
  obtain ⟨G, instG, hR⟩ := cp_to_stinespring a.toBasis Q hQ
  letI := instG
  obtain ⟨R, hR⟩ := hR
  have hR' : dilationChannel R = Q := by
    ext1 X
    exact (hR X).symm
  obtain ⟨W, hW, herr⟩ := filter_of_slack_dilation V M R
    (by simpa only [hM', hR'] using hdom)
  refine ⟨W, by simpa only [hM'] using hW, herr.trans ?_⟩
  exact dilation_norm_le_sqrt_of_trace_bound R ε hε (by simpa only [hR'] using htrace)

end QuantumChannelContinuity


