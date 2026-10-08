-- Prove2me | Definitions.Def_CRCD_Quantum_QuantumEntropy_SandwichedRenyiRelativeEntropy_part_2
-- name    : CRCD_Quantum_QuantumEntropy_SandwichedRenyiRelativeEntropy_part_2
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-08T00:55:18.401515+00:00
-- url     : https://prove2.me/theorems/28b8bcbf-b010-4f2a-a045-86768cd8798c
-- title:
--   Variational optimizers and concavity of conjugated trace powers
-- statement:
--   On a nonzero finite-dimensional complex Hilbert space, use the preceding trace functionals $Q_\alpha,V_\alpha,T_p,F_p$ and the positive-definite cone $\mathcal P$. Define the operator optimizer
--   $$
--   X_*=P(P\rho P)^{\alpha-1}P,\qquad P=\sigma^{(1-\alpha)/(2\alpha)}.
--   $$
--   For $\rho,\sigma>0$ and $\alpha>0$, $\alpha\ne1$, one has $X_*>0$ and $V_\alpha(\rho,\sigma;X_*)=Q_\alpha(\rho\Vert\sigma)$, separately proved for $\alpha>1$ and $0<\alpha<1$.
--
--   For invertible $B$ and $A>0$, the positive-exponent variational bound is attained when $0<p\le1$. The part proves
--   $$
--   A\longmapsto T_p(B,A)=\operatorname{Re}\operatorname{Tr}[(B^*A^pB)^{1/p}]
--   \quad\text{is concave on }\mathcal P\quad(-1\le p\le1,\ p\ne0).
--   $$
--   The supporting functional $F_p(B,A,X)$ is jointly convex for $-1\le p<0$ and jointly concave for $0<p<1$. For fixed $X>0$, the $\sigma$-term $\operatorname{Re}\operatorname{Tr}[(\sigma^{(\alpha-1)/(2\alpha)}X\sigma^{(\alpha-1)/(2\alpha)})^{\alpha/(\alpha-1)}]$ is concave on $\mathcal P$ when $\alpha\ge1/2$ and $\alpha\ne1$, and $\operatorname{Re}V_\alpha(\rho,\sigma;X)$ is jointly convex on $\mathcal P^2$ for $\alpha>1$. Cyclic trace identities, equality of the power traces of $C^*C$ and $CC^*$ for invertible $C$, real-scalar trace linearity, and positivity of conjugated powers supply the algebraic identities used in these statements. Operators are not required to have unit trace.
-- source:
--   https://github.com/Hayata-Yamasaki-Group/lean-quantum/blob/bf1c4f6aaec84948f1a1c76c0728432813404a0f/Quantum/QuantumEntropy/SandwichedRenyiRelativeEntropy.lean#L839-L1450

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
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
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
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.LinearMapPiProd
import Mathlib.Topology.Algebra.Star.Unitary
import Definitions.Def_CRCD_Quantum_QuantumEntropy_HaarUnitary
import Definitions.Def_CRCD_Quantum_QuantumEntropy_SandwichedRenyiRelativeEntropy_part_1
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
Copyright (c) 2025 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/








open QuantumState
open scoped ComplexOrder NNReal Topology

namespace SandwichedRenyiRelativeEntropy

section Definition

open LiebAndoTrace GeneralizedPerspectiveFunction

universe uDef

variable {ℋ : Type uDef} [Qudit ℋ]







variable [Nontrivial ℋ]











end Definition

section VariationalRepresentation

universe u

variable {ℋ : Type u} [Qudit ℋ]

set_option linter.style.longLine false





















end VariationalRepresentation

section LiebAndoLinearMap

open LiebAndoTrace GeneralizedPerspectiveFunction

universe u'

variable {ℋ : Type u'} [Qudit ℋ]
variable [Nontrivial ℋ]









end LiebAndoLinearMap

section TraceConjPowConcavity

open LiebAndoTrace GeneralizedPerspectiveFunction

universe u''

variable {ℋ : Type u''} [Qudit ℋ] [Nontrivial ℋ]

set_option linter.style.longLine false































omit [Nontrivial ℋ] in
set_option backward.isDefEq.respectTransparency false in
/-- Variational attainment (0 < p ≤ 1):
    ∃ X_opt ∈ pdSetLM achieving equality. -/
 lemma exists_traceConjPowVar_eq_pos {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1)
    {B A : L ℋ} (hB : IsUnit B) (hA : A ∈ pdSetLM (ℋ := ℋ)) :
    ∃ X ∈ pdSetLM (ℋ := ℋ),
      p * traceConjPow (ℋ := ℋ) p B A = traceConjPowVar (ℋ := ℋ) p B A X := by
  rcases eq_or_lt_of_le hp1 with rfl | hp1'
  · -- p = 1: traceConjPowVar 1 B A X = Tr(B† A B).re, = 1 * traceConjPow
    refine ⟨A, hA, ?_⟩
    have hA_nn := nonneg_of_pdSetLM hA
    have hM_nn : (0 : L ℋ) ≤ star B * A * B := star_left_conjugate_nonneg hA_nn _
    have h1 : (1 : ℝ) / 1 = (1 : ℝ) := by norm_num
    have eq1 : CFC.rpow A (1 : ℝ) = A := CFC.rpow_one _ hA_nn
    have eq2 : CFC.rpow (star B * A * B) (1 : ℝ) = star B * A * B :=
      CFC.rpow_one _ hM_nn
    have hfun : traceConjPow (ℋ := ℋ) 1 B A = (Tr (star B * A * B)).re := by
      simp only [traceConjPow, h1, eq1, eq2]
    have hvar : traceConjPowVar (ℋ := ℋ) 1 B A A = (Tr (star B * A * B)).re := by
      unfold traceConjPowVar
      have h0 : (1 : ℝ) - 1 = 0 := by ring
      rw [h0, zero_mul, sub_zero]
      have eq0 : CFC.rpow A (0 : ℝ) = 1 := CFC.rpow_zero _ hA_nn
      have h_bridge := _root_.SandwichedRenyiRelativeEntropy.liebTraceMapLM_as_lm_trace (by linarith : (0 : ℝ) ≤ 1) le_rfl B A A hA_nn hA_nn
      simp only [h0, eq0, eq1, mul_one] at h_bridge
      exact h_bridge
    rw [hfun, hvar, one_mul]
  · -- 0 < p < 1
    have hA_nn := nonneg_of_pdSetLM hA
    set M := star B * CFC.rpow A p * B with hM_def
    have hM_nn : (0 : L ℋ) ≤ M := star_left_conjugate_nonneg CFC.rpow_nonneg _
    have hApd : CFC.rpow A p ∈ pdSetLM (ℋ := ℋ) := _root_.SandwichedRenyiRelativeEntropy.pdSetLM_rpow hA
    have hMpd : M ∈ pdSetLM (ℋ := ℋ) := pdSetLM_conj hApd hB
    have hM_unit : IsUnit M := isUnit_of_pdSetLM hMpd
    set X_opt := CFC.rpow M (1 / p) with hX_opt_def
    have h1p_pos : 0 < 1 / p := by positivity
    have hX_opt_pd : X_opt ∈ pdSetLM (ℋ := ℋ) := _root_.SandwichedRenyiRelativeEntropy.pdSetLM_rpow hMpd
    refine ⟨X_opt, hX_opt_pd, ?_⟩
    have hX_opt_nn := nonneg_of_pdSetLM hX_opt_pd
    have h_bridge := _root_.SandwichedRenyiRelativeEntropy.liebTraceMapLM_as_lm_trace hp0.le hp1 B A X_opt hA_nn hX_opt_nn
    have h1_sub_p_nn : 0 ≤ 1 - p := by linarith
    have hrpow_comp : CFC.rpow X_opt (1 - p) = CFC.rpow M ((1 - p) / p) := by
      rw [hX_opt_def]
      simp only [CFC.rpow_eq_pow]
      rw [CFC.rpow_rpow_of_exponent_nonneg M (1 / p) (1 - p) (by positivity) h1_sub_p_nn]
      congr 1; ring
    have hrpow_mul : M * CFC.rpow M ((1 - p) / p) = X_opt := by
      have h1 : CFC.rpow M 1 = M := CFC.rpow_one M hM_nn
      have hpne : (p : ℝ) ≠ 0 := ne_of_gt hp0
      have hexp : (1 : ℝ) + (1 - p) / p = 1 / p := by field_simp; ring
      have hadd : CFC.rpow M 1 * CFC.rpow M ((1 - p) / p) =
          CFC.rpow M (1 + (1 - p) / p) := by
        simp only [CFC.rpow_eq_pow]
        exact (CFC.rpow_add hM_unit).symm
      conv_lhs => lhs; rw [← h1]
      rw [hadd, hexp]
    unfold traceConjPowVar traceConjPow
    rw [h_bridge, hrpow_comp, ← hM_def, hrpow_mul]
    ring

omit [Nontrivial ℋ] in
 lemma real_smul_eq_complex_smul (r : ℝ) (X : L ℋ) :
    (r • X : L ℋ) = ((↑r : ℂ) • X : L ℋ) :=
  LinearMap.ext fun x => by
    simp only [LinearMap.smul_apply]
    change r • X x = (↑r : ℂ) • X x
    haveI : IsScalarTower ℝ ℂ ℋ := ⟨fun r c x => by
      change (r • c) • x = ((r : ℂ)) • c • x
      rw [Algebra.smul_def, mul_smul]; simp [RCLike.algebraMap_eq_ofReal]⟩
    exact algebraMap_smul ℂ r (X x)

omit [Nontrivial ℋ] in
 lemma traceRe_real_smul (r : ℝ) (X : L ℋ) :
    (LinearMap.trace ℂ ℋ (r • X)).re = r * (LinearMap.trace ℂ ℋ X).re := by
  rw [_root_.SandwichedRenyiRelativeEntropy.real_smul_eq_complex_smul r X, map_smul, smul_eq_mul, Complex.re_ofReal_mul]

omit [Nontrivial ℋ] in
 lemma trace_re_convex_combo (θ : ℝ) (X₁ X₂ : L ℋ) :
    (Tr ((1 - θ) • X₁ + θ • X₂)).re =
      (1 - θ) * (Tr X₁).re + θ * (Tr X₂).re := by
  rw [map_add, Complex.add_re, _root_.SandwichedRenyiRelativeEntropy.traceRe_real_smul, _root_.SandwichedRenyiRelativeEntropy.traceRe_real_smul]

omit [Nontrivial ℋ] in
/-- Cyclic trace: Tr(A^s K† B^{1-s} K) = Tr(B^{1-s} K A^s K†).
    Equivalently: liebTraceMapLM(s,K,A,B) = liebTraceMapLM(1−s,star K,B,A). -/
 lemma traceRe_mul_comm (X Y : LownerHeinzTheorem.L ℋ) :
    traceRe (ℋ := ℋ) (X * Y) = traceRe (ℋ := ℋ) (Y * X) := by
  simp only [traceRe]
  exact congrArg Complex.re
    (LinearMap.trace_mul_comm (R := ℂ) (M := ℋ) X.toLinearMap Y.toLinearMap)

omit [Nontrivial ℋ] in
 lemma liebTraceMapLM_cyclic (s : ℝ) (K A B : L ℋ) :
    liebTraceMapLM (ℋ := ℋ) s K A B =
      liebTraceMapLM (ℋ := ℋ) (1 - s) (star K) B A := by
  simp only [liebTraceMapLM, liebTraceMap]
  rw [_root_.SandwichedRenyiRelativeEntropy.star_toCLM, star_star, show (1 : ℝ) - (1 - s) = s from by ring]
  change traceRe (ℋ := ℋ)
      (A.toContinuousLinearMap ^ s * star K.toContinuousLinearMap *
        B.toContinuousLinearMap ^ (1 - s) * K.toContinuousLinearMap) =
    traceRe (ℋ := ℋ)
      (B.toContinuousLinearMap ^ (1 - s) * K.toContinuousLinearMap *
        A.toContinuousLinearMap ^ s * star K.toContinuousLinearMap)
  have h := _root_.SandwichedRenyiRelativeEntropy.traceRe_mul_comm (ℋ := ℋ)
    (A.toContinuousLinearMap ^ s * star K.toContinuousLinearMap)
    (B.toContinuousLinearMap ^ (1 - s) * K.toContinuousLinearMap)
  simp only [mul_assoc] at h ⊢
  exact h

 lemma traceConjPowVar_jointlyConvex {p : ℝ} (hpm1 : -1 ≤ p) (hp0 : p < 0) (B : L ℋ) :
    JointlyConvexOn (pdSetLM (ℋ := ℋ)) (pdSetLM (ℋ := ℋ))
      (fun A X => traceConjPowVar (ℋ := ℋ) p B A X) := by
  intro A₁ A₂ X₁ X₂ θ hA₁ hA₂ hX₁ hX₂ hθ0 hθ1
  simp only [smul_eq_mul, traceConjPowVar]
  simp only [_root_.SandwichedRenyiRelativeEntropy.liebTraceMapLM_cyclic p (star B), star_star]
  have h_ando := liebTrace_jointlyConvexOn_pdSet_lm (show (1 : ℝ) ≤ 1 - p by linarith)
    (show 1 - p ≤ 2 by linarith) (B : L ℋ)
  have h_swap : JointlyConvexOn (pdSetLM (ℋ := ℋ)) (pdSetLM (ℋ := ℋ))
      (fun A X => liebTraceMapLM (ℋ := ℋ) (1 - p) B X A) :=
    fun _ _ _ _ _ h1 h2 h3 h4 h5 h6 => h_ando h3 h4 h1 h2 h5 h6
  have h_conv := h_swap hA₁ hA₂ hX₁ hX₂ hθ0 hθ1
  simp only [smul_eq_mul] at h_conv
  have h_tr := _root_.SandwichedRenyiRelativeEntropy.trace_re_convex_combo θ X₁ X₂
  nlinarith

/-- Joint concavity of `traceConjPowVar` for 0 < p < 1.
    By Lieb's concavity theorem liebTraceMapLM(p, B†, A, X) is jointly concave,
    and the trace penalty is linear, so the functional is jointly concave. -/
 lemma traceConjPowVar_jointlyConcave {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (B : L ℋ) :
    JointlyConcaveOn (pdSetLM (ℋ := ℋ)) (pdSetLM (ℋ := ℋ))
      (fun A X => traceConjPowVar (ℋ := ℋ) p B A X) := by
  intro A₁ A₂ X₁ X₂ θ hA₁ hA₂ hX₁ hX₂ hθ0 hθ1
  simp only [smul_eq_mul, traceConjPowVar]
  have h_lieb := liebTrace_jointlyConcaveOn_pdSet_lm hp0 hp1 (star B : L ℋ)
    hA₁ hA₂ hX₁ hX₂ hθ0 hθ1
  simp only [smul_eq_mul] at h_lieb
  have h_tr := _root_.SandwichedRenyiRelativeEntropy.trace_re_convex_combo θ X₁ X₂
  nlinarith

set_option backward.isDefEq.respectTransparency false in
/-- Concavity of `A ↦ Tr((B† A^p B)^{1/p})` on `pdSetLM` for `−1 ≤ p < 0`.
    Proof: The variational functional `F(A, X)` is jointly convex in `(A, X)` by Ando's theorem.
    Since `p · traceConjPow = inf_X F`, the function `p · traceConjPow` is convex.
    Dividing by `p < 0` gives concavity of `traceConjPow`. -/
theorem traceConjPow_concave_neg {p : ℝ} (hpm1 : -1 ≤ p) (hp0 : p < 0) (B : L ℋ) (hB : IsUnit B) :
    ConcaveOn ℝ (pdSetLM (ℋ := ℋ)) (traceConjPow (ℋ := ℋ) p B) := by
  refine ⟨_root_.SandwichedRenyiRelativeEntropy.pdSetLM_convex, ?_⟩
  intro x hx y hy a b ha hb hab
  simp only [smul_eq_mul]
  have hab' : a = 1 - b := by linarith
  have hb1 : b ≤ 1 := by linarith
  obtain ⟨Xx, hXx_mem, hXx_eq⟩ := _root_.SandwichedRenyiRelativeEntropy.exists_traceConjPowVar_eq_neg hp0 hB hx
  obtain ⟨Xy, hXy_mem, hXy_eq⟩ := _root_.SandwichedRenyiRelativeEntropy.exists_traceConjPowVar_eq_neg hp0 hB hy
  have h_combo : a • x + b • y ∈ pdSetLM (ℋ := ℋ) := by
    rw [hab']; exact pdSetLM_convexCombo hx hy hb hb1
  have h_Xcombo : a • Xx + b • Xy ∈ pdSetLM (ℋ := ℋ) := by
    rw [hab']; exact pdSetLM_convexCombo hXx_mem hXy_mem hb hb1
  have step1 : p * traceConjPow (ℋ := ℋ) p B (a • x + b • y) ≤
      traceConjPowVar (ℋ := ℋ) p B (a • x + b • y) (a • Xx + b • Xy) := by
    rw [hab'] at h_combo h_Xcombo ⊢; exact _root_.SandwichedRenyiRelativeEntropy.traceConjPowVar_le_neg hp0 hB h_combo h_Xcombo
  rw [hab'] at step1
  have step2 := _root_.SandwichedRenyiRelativeEntropy.traceConjPowVar_jointlyConvex hpm1 hp0 B hx hy hXx_mem hXy_mem hb hb1
  simp only [smul_eq_mul] at step2
  have step3 : (1 - b) * traceConjPowVar (ℋ := ℋ) p B x Xx + b * traceConjPowVar (ℋ := ℋ) p B y Xy =
      p * ((1 - b) * traceConjPow (ℋ := ℋ) p B x + b * traceConjPow (ℋ := ℋ) p B y) := by
    rw [← hXx_eq, ← hXy_eq]; ring
  have h_chain : p * traceConjPow (ℋ := ℋ) p B ((1 - b) • x + b • y) ≤
      p * ((1 - b) * traceConjPow (ℋ := ℋ) p B x + b * traceConjPow (ℋ := ℋ) p B y) :=
    calc p * traceConjPow (ℋ := ℋ) p B ((1 - b) • x + b • y)
        ≤ traceConjPowVar (ℋ := ℋ) p B ((1 - b) • x + b • y) ((1 - b) • Xx + b • Xy) := step1
      _ ≤ (1 - b) * traceConjPowVar (ℋ := ℋ) p B x Xx + b * traceConjPowVar (ℋ := ℋ) p B y Xy := step2
      _ = p * ((1 - b) * traceConjPow (ℋ := ℋ) p B x + b * traceConjPow (ℋ := ℋ) p B y) := step3
  rw [hab']
  by_contra h_neg
  push_neg at h_neg
  have := mul_lt_mul_of_neg_left h_neg hp0
  linarith

set_option backward.isDefEq.respectTransparency false in
/-- Concavity of `A ↦ Tr((B† A^p B)^{1/p})` on `pdSetLM` for `0 < p ≤ 1`.
    Proof: `F` is jointly concave by Lieb's theorem; `p · traceConjPow = sup_X F` is concave;
    dividing by `p > 0` preserves concavity. -/
theorem traceConjPow_concave_pos {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) (B : L ℋ) (hB : IsUnit B) :
    ConcaveOn ℝ (pdSetLM (ℋ := ℋ)) (traceConjPow (ℋ := ℋ) p B) := by
  refine ⟨_root_.SandwichedRenyiRelativeEntropy.pdSetLM_convex, ?_⟩
  intro x hx y hy a b ha hb hab
  simp only [smul_eq_mul]
  have hab' : a = 1 - b := by linarith
  have hb1 : b ≤ 1 := by linarith
  have hp1' : p < 1 ∨ p = 1 := lt_or_eq_of_le hp1
  obtain ⟨Xx, hXx_mem, hXx_eq⟩ := _root_.SandwichedRenyiRelativeEntropy.exists_traceConjPowVar_eq_pos hp0 hp1 hB hx
  obtain ⟨Xy, hXy_mem, hXy_eq⟩ := _root_.SandwichedRenyiRelativeEntropy.exists_traceConjPowVar_eq_pos hp0 hp1 hB hy
  have h_combo : a • x + b • y ∈ pdSetLM (ℋ := ℋ) := by
    rw [hab']; exact pdSetLM_convexCombo hx hy hb hb1
  have h_Xcombo : a • Xx + b • Xy ∈ pdSetLM (ℋ := ℋ) := by
    rw [hab']; exact pdSetLM_convexCombo hXx_mem hXy_mem hb hb1
  have step1 : traceConjPowVar (ℋ := ℋ) p B (a • x + b • y) (a • Xx + b • Xy) ≤
      p * traceConjPow (ℋ := ℋ) p B (a • x + b • y) := by
    rw [hab'] at h_combo h_Xcombo ⊢; exact _root_.SandwichedRenyiRelativeEntropy.traceConjPowVar_le_pos hp0 hp1 h_combo h_Xcombo
  rw [hab'] at step1
  rcases hp1' with hp1' | rfl
  · have step2 := _root_.SandwichedRenyiRelativeEntropy.traceConjPowVar_jointlyConcave hp0 hp1' B hx hy hXx_mem hXy_mem hb hb1
    simp only [smul_eq_mul] at step2
    have step3 : p * ((1 - b) * traceConjPow (ℋ := ℋ) p B x + b * traceConjPow (ℋ := ℋ) p B y) =
        (1 - b) * traceConjPowVar (ℋ := ℋ) p B x Xx + b * traceConjPowVar (ℋ := ℋ) p B y Xy := by
      rw [← hXx_eq, ← hXy_eq]; ring
    have h_chain : p * ((1 - b) * traceConjPow (ℋ := ℋ) p B x + b * traceConjPow (ℋ := ℋ) p B y) ≤
        p * traceConjPow (ℋ := ℋ) p B ((1 - b) • x + b • y) :=
      calc p * ((1 - b) * traceConjPow (ℋ := ℋ) p B x + b * traceConjPow (ℋ := ℋ) p B y)
          = (1 - b) * traceConjPowVar (ℋ := ℋ) p B x Xx + b * traceConjPowVar (ℋ := ℋ) p B y Xy := step3
        _ ≤ traceConjPowVar (ℋ := ℋ) p B ((1 - b) • x + b • y) ((1 - b) • Xx + b • Xy) := step2
        _ ≤ p * traceConjPow (ℋ := ℋ) p B ((1 - b) • x + b • y) := step1
    rw [hab']
    by_contra h_neg
    push_neg at h_neg
    have := mul_lt_mul_of_pos_left h_neg hp0
    linarith
  · -- p = 1: A ↦ Tr(B†AB) is affine, hence concave
    have nn_of_pd_lm : ∀ {A : L ℋ}, A ∈ pdSetLM (ℋ := ℋ) → (0 : L ℋ) ≤ A := by
      intro A hA
      have h_clm_nn : (0 : LownerHeinzTheorem.L ℋ) ≤ A.toContinuousLinearMap := by
        obtain ⟨hA_sa, hA_spec⟩ := hA
        exact (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) _ (ha := hA_sa)).2
          (fun r hr => (hA_spec hr).le)
      rw [LinearMap.nonneg_iff_isPositive]
      have h := (ContinuousLinearMap.nonneg_iff_isPositive _).mp h_clm_nn
      exact ⟨fun x y => h.1 x y, fun x => h.2 x⟩
    have hfun : ∀ {A : L ℋ}, A ∈ pdSetLM (ℋ := ℋ) →
        traceConjPow (ℋ := ℋ) 1 B A = (Tr (star B * A * B)).re := by
      intro A hA
      unfold traceConjPow
      have h1 : (1 : ℝ) / 1 = (1 : ℝ) := by norm_num
      have eq1 : CFC.rpow A 1 = A := CFC.rpow_one _ (nn_of_pd_lm hA)
      have eq2 : CFC.rpow (star B * A * B) 1 = star B * A * B :=
        CFC.rpow_one _ (star_left_conjugate_nonneg (nn_of_pd_lm hA) _)
      simp only [h1, eq1, eq2]
    rw [hfun hx, hfun hy, hfun h_combo]
    have hmul : (star B * (a • x + b • y) * B : L ℋ) =
        a • (star B * x * B) + b • (star B * y * B) := by
      simp only [mul_add, add_mul, smul_mul_assoc, mul_smul_comm]
    rw [hmul, map_add, Complex.add_re, _root_.SandwichedRenyiRelativeEntropy.traceRe_real_smul, _root_.SandwichedRenyiRelativeEntropy.traceRe_real_smul]

set_option backward.isDefEq.respectTransparency false in
/-- For a fixed operator `B`, the map `A ↦ Tr((B† A^p B)^{1/p})` is concave
    on positive-definite operators for `−1 ≤ p ≤ 1`, `p ≠ 0` (Frank–Lieb concavity). -/
theorem traceConjPow_concave {p : ℝ} (hp_neg : -1 ≤ p) (hp_pos : p ≤ 1) (hp_ne : p ≠ 0) (B : L ℋ)
    (hB : IsUnit B) :
    ConcaveOn ℝ (pdSetLM (ℋ := ℋ)) (traceConjPow (ℋ := ℋ) p B) := by
  rcases lt_or_ge p 0 with hp | hp
  · exact traceConjPow_concave_neg hp_neg hp B hB
  · exact traceConjPow_concave_pos (lt_of_le_of_ne hp (Ne.symm hp_ne)) hp_pos B hB

end TraceConjPowConcavity

section JointConvexity

open LiebAndoTrace GeneralizedPerspectiveFunction
open scoped MatrixOrder

universe u₃

variable {ℋ : Type u₃} [Qudit ℋ] [Nontrivial ℋ]

set_option backward.isDefEq.respectTransparency false
set_option linter.style.longLine false

omit [Nontrivial ℋ] in
/-- Eigenvalue similarity: CC† and C†C have identical rpow traces.
    Both CC† and C†C have the same non-zero eigenvalues, so Tr(f(CC†)) = Tr(f(C†C))
    for any CFC function f (including rpow). -/
 lemma trace_rpow_star_mul_comm {C : L ℋ} (hC : IsUnit C) (q : ℝ) :
    Tr (CFC.rpow (star C * C) q) = Tr (CFC.rpow (C * star C) q) := by
  have h1_nn : (0 : L ℋ) ≤ 1 :=
    (LinearMap.nonneg_iff_isPositive 1).mpr LinearMap.isPositive_one
  have h_sCC_nn : (0 : L ℋ) ≤ star C * C := by
    have := star_left_conjugate_nonneg h1_nn C; rwa [mul_one] at this
  have h_CsC_nn : (0 : L ℋ) ≤ C * star C := by
    have := star_left_conjugate_nonneg h1_nn (star C); rwa [star_star, mul_one] at this
  have h_sCC_pos := (LinearMap.nonneg_iff_isPositive _).mp h_sCC_nn
  have h_CsC_pos := (LinearMap.nonneg_iff_isPositive _).mp h_CsC_nn
  have h_sCC_unit : IsUnit (star C * C) := hC.star.mul hC
  have h_CsC_unit : IsUnit (C * star C) := hC.mul hC.star
  let b := stdOrthonormalBasis ℂ ℋ
  set M := LinearMap.toMatrixOrthonormal b C
  have hH1 : (star M * M).IsHermitian := Matrix.isHermitian_conjTranspose_mul_self M
  have hH2 : (M * star M).IsHermitian := Matrix.isHermitian_mul_conjTranspose_self M
  have hNN1 : 0 ≤ star M * M := (Matrix.posSemidef_conjTranspose_mul_self M).nonneg
  have hNN2 : 0 ≤ M * star M := (Matrix.posSemidef_self_mul_conjTranspose M).nonneg
  have h_φ_sCC : LinearMap.toMatrixOrthonormal b (star C * C) = star M * M := by
    rw [map_mul, map_star]
  have h_φ_CsC : LinearMap.toMatrixOrthonormal b (C * star C) = M * star M := by
    rw [map_mul, map_star]
  have h_eig : hH1.eigenvalues = hH2.eigenvalues := by
    rw [Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff]
    exact Matrix.charpoly_mul_comm (star M) M
  calc Tr (CFC.rpow (star C * C) q)
      = Matrix.trace (LinearMap.toMatrixOrthonormal b (CFC.rpow (star C * C) q)) :=
        tr_eq_matrix_trace_orthonormal b _
    _ = Matrix.trace (CFC.rpow (LinearMap.toMatrixOrthonormal b (star C * C)) q) := by
        rw [toMatrixOrthonormal_rpow_pd b _ h_sCC_pos h_sCC_unit q]
    _ = Matrix.trace (CFC.rpow (star M * M) q) := by rw [h_φ_sCC]
    _ = ∑ i, (((hH1.eigenvalues i) ^ q : ℝ) : ℂ) :=
        matrix_trace_rpow_eq_sum_eigenvalues _ hH1 hNN1 q
    _ = ∑ i, (((hH2.eigenvalues i) ^ q : ℝ) : ℂ) := by rw [h_eig]
    _ = Matrix.trace (CFC.rpow (M * star M) q) :=
        (matrix_trace_rpow_eq_sum_eigenvalues _ hH2 hNN2 q).symm
    _ = Matrix.trace (CFC.rpow (LinearMap.toMatrixOrthonormal b (C * star C)) q) := by
        rw [h_φ_CsC]
    _ = Matrix.trace (LinearMap.toMatrixOrthonormal b (CFC.rpow (C * star C) q)) := by
        rw [toMatrixOrthonormal_rpow_pd b _ h_CsC_pos h_CsC_unit q]
    _ = Tr (CFC.rpow (C * star C) q) :=
        (tr_eq_matrix_trace_orthonormal b _).symm

omit [Nontrivial ℋ] in
set_option backward.isDefEq.respectTransparency false in
/-- The σ-dependent part of quasiVar equals traceConjPow via eigenvalue similarity:
    Re Tr((σ^β H σ^β)^q) = traceConjPow((α-1)/α, H^{1/2}, σ)
    where β = (α-1)/(2α), q = α/(α-1). -/
 lemma quasiVar_sigma_eq_traceConjPow {α : ℝ} (hα0 : 0 < α)
    {H σ : L ℋ} (hH : H ∈ pdSetLM (ℋ := ℋ)) (hσ : σ ∈ pdSetLM (ℋ := ℋ)) :
    (Tr (CFC.rpow (CFC.rpow σ ((α - 1) / (2 * α)) * H * CFC.rpow σ ((α - 1) / (2 * α)))
         (α / (α - 1)))).re =
    traceConjPow (ℋ := ℋ) ((α - 1) / α) (CFC.rpow H (1/2)) σ := by
  set P := CFC.rpow σ ((α - 1) / (2 * α))
  set Q := CFC.rpow H (1/2)
  set C := P * Q
  have hH_nn := nonneg_of_pdSetLM hH
  have hσ_nn := nonneg_of_pdSetLM hσ
  have hH_unit := isUnit_of_pdSetLM hH
  have hσ_unit := isUnit_of_pdSetLM hσ
  have hP_sa : IsSelfAdjoint P := IsSelfAdjoint.of_nonneg CFC.rpow_nonneg
  have hQ_sa : IsSelfAdjoint Q := IsSelfAdjoint.of_nonneg CFC.rpow_nonneg
  have hP_unit : IsUnit P := hσ_unit.cfcRpow _ hσ_nn
  have hQ_unit : IsUnit Q := hH_unit.cfcRpow _ hH_nn
  have hC_unit : IsUnit C := hP_unit.mul hQ_unit
  have h_QQ : Q * Q = H := by
    change CFC.rpow H (1/2) * CFC.rpow H (1/2) = H
    have : CFC.rpow H (1/2) * CFC.rpow H (1/2) = CFC.rpow H (1/2 + 1/2) := by
      simp only [CFC.rpow_eq_pow]; exact (CFC.rpow_add hH_unit).symm
    rw [this, show (1 : ℝ)/2 + 1/2 = 1 from by norm_num]
    exact CFC.rpow_one H hH_nn
  have h_PP : P * P = CFC.rpow σ ((α - 1) / α) := by
    change CFC.rpow σ ((α - 1) / (2 * α)) * CFC.rpow σ ((α - 1) / (2 * α)) =
      CFC.rpow σ ((α - 1) / α)
    have : CFC.rpow σ ((α - 1) / (2 * α)) * CFC.rpow σ ((α - 1) / (2 * α)) =
        CFC.rpow σ ((α - 1) / (2 * α) + (α - 1) / (2 * α)) := by
      simp only [CFC.rpow_eq_pow]; exact (CFC.rpow_add hσ_unit).symm
    rw [this]; congr 1; field_simp; ring
  have h_star_C : star C = Q * P := by
    change star (P * Q) = Q * P
    rw [star_mul, hP_sa.star_eq, hQ_sa.star_eq]
  have h_CsC : C * star C = P * H * P := by
    rw [h_star_C]
    change P * Q * (Q * P) = P * H * P
    rw [← mul_assoc (P * Q) Q P, mul_assoc P Q Q, h_QQ]
  have h_sCC : star C * C = Q * CFC.rpow σ ((α - 1) / α) * Q := by
    rw [h_star_C]
    change Q * P * (P * Q) = Q * CFC.rpow σ ((α - 1) / α) * Q
    rw [← mul_assoc (Q * P) P Q, mul_assoc Q P P, h_PP]
  suffices h : Tr (CFC.rpow (P * H * P) (α / (α - 1))) =
    Tr (CFC.rpow (Q * CFC.rpow σ ((α - 1) / α) * Q) (α / (α - 1))) by
    unfold traceConjPow
    rw [hQ_sa.star_eq, show (1 : ℝ) / ((α - 1) / α) = α / (α - 1) from by field_simp]
    exact congrArg Complex.re h
  calc Tr (CFC.rpow (P * H * P) (α / (α - 1)))
      = Tr (CFC.rpow (C * star C) (α / (α - 1))) := by rw [← h_CsC]
    _ = Tr (CFC.rpow (star C * C) (α / (α - 1))) :=
        (_root_.SandwichedRenyiRelativeEntropy.trace_rpow_star_mul_comm hC_unit _).symm
    _ = Tr (CFC.rpow (Q * CFC.rpow σ ((α - 1) / α) * Q) (α / (α - 1))) := by
        rw [h_sCC]

set_option backward.isDefEq.respectTransparency false in
/-- Concavity of the σ-term on `pdSetLM`: `σ ↦ Re Tr((σ^β H σ^β)^q)` is concave
    for `1/2 ≤ α`, `α ≠ 1` and `H ∈ pdSetLM`.
    Uses `traceConjPow_concave` and eigenvalue similarity. -/
lemma sigma_term_concaveOn {α : ℝ} (hα0 : 0 < α) (hα_ne1 : α ≠ 1) (hα_ge : 1 / 2 ≤ α)
    {H : L ℋ} (hH : H ∈ pdSetLM (ℋ := ℋ)) :
    ConcaveOn ℝ (pdSetLM (ℋ := ℋ)) (fun σ =>
      (Tr (CFC.rpow (CFC.rpow σ ((α - 1) / (2 * α)) * H * CFC.rpow σ ((α - 1) / (2 * α)))
           (α / (α - 1)))).re) := by
  set p := (α - 1) / α with hp_def
  have hp_ge : -1 ≤ p := by rw [hp_def]; rw [le_div_iff₀ hα0]; linarith
  have hp_le : p ≤ 1 := by rw [hp_def]; rw [div_le_one hα0]; linarith
  have hp_ne : p ≠ 0 := by rw [hp_def]; exact div_ne_zero (sub_ne_zero.mpr hα_ne1) (ne_of_gt hα0)
  have hH_nn := nonneg_of_pdSetLM hH
  have hH_unit := isUnit_of_pdSetLM hH
  have hHsq_unit : IsUnit (CFC.rpow H (1/2)) := hH_unit.cfcRpow (1/2) hH_nn
  have h_concave := traceConjPow_concave hp_ge hp_le hp_ne (CFC.rpow H (1/2)) hHsq_unit
  refine ⟨_root_.SandwichedRenyiRelativeEntropy.pdSetLM_convex, ?_⟩
  intro σ₁ hσ₁ σ₂ hσ₂ a b ha hb hab
  simp only [smul_eq_mul]
  have h_combo : a • σ₁ + b • σ₂ ∈ pdSetLM (ℋ := ℋ) := by
    rw [show a = 1 - b from by linarith]
    exact pdSetLM_convexCombo hσ₁ hσ₂ hb (by linarith)
  rw [_root_.SandwichedRenyiRelativeEntropy.quasiVar_sigma_eq_traceConjPow hα0 hH hσ₁,
      _root_.SandwichedRenyiRelativeEntropy.quasiVar_sigma_eq_traceConjPow hα0 hH hσ₂,
      _root_.SandwichedRenyiRelativeEntropy.quasiVar_sigma_eq_traceConjPow hα0 hH h_combo]
  exact h_concave.2 hσ₁ hσ₂ ha hb hab

/-- The variational optimizer: `H_opt = P (P ρ P)^{α-1} P` with `P = σ^{(1-α)/(2α)}`. -/
noncomputable def quasiVarOpt (α : ℝ) (ρ σ : L ℋ) : L ℋ :=
  CFC.rpow σ ((1 - α) / (2 * α)) *
    CFC.rpow (CFC.rpow σ ((1 - α) / (2 * α)) * ρ *
      CFC.rpow σ ((1 - α) / (2 * α))) (α - 1) *
    CFC.rpow σ ((1 - α) / (2 * α))

omit [Nontrivial ℋ] in
 lemma rpow_conj_pdSetLM {β q : ℝ}
    {ρ σ : L ℋ} (hρ : ρ ∈ pdSetLM (ℋ := ℋ)) (hσ : σ ∈ pdSetLM (ℋ := ℋ)) :
    star (CFC.rpow σ β) * CFC.rpow (star (CFC.rpow σ β) * ρ *
      CFC.rpow σ β) q * CFC.rpow σ β ∈ pdSetLM (ℋ := ℋ) := by
  have hP_pd : CFC.rpow σ β ∈ pdSetLM (ℋ := ℋ) := pdSetLM_rpow_ne hσ
  have hP_unit := isUnit_of_pdSetLM hP_pd
  exact pdSetLM_conj (pdSetLM_rpow_ne (pdSetLM_conj hρ hP_unit)) hP_unit

omit [Nontrivial ℋ] in
set_option backward.isDefEq.respectTransparency false in
lemma quasiVarOpt_pdSetLM {α : ℝ} (hα0 : 0 < α) (hα_ne1 : α ≠ 1)
    {ρ σ : L ℋ} (hρ : ρ ∈ pdSetLM (ℋ := ℋ)) (hσ : σ ∈ pdSetLM (ℋ := ℋ)) :
    quasiVarOpt α ρ σ ∈ pdSetLM (ℋ := ℋ) := by
  have hβ'_ne : (1 - α) / (2 * α) ≠ 0 :=
    div_ne_zero (sub_ne_zero.mpr (Ne.symm hα_ne1)) (by positivity)
  have hα1_ne : (α - 1 : ℝ) ≠ 0 := sub_ne_zero.mpr hα_ne1
  have hP_sa : IsSelfAdjoint (CFC.rpow σ ((1 - α) / (2 * α))) :=
    IsSelfAdjoint.of_nonneg CFC.rpow_nonneg
  have key := _root_.SandwichedRenyiRelativeEntropy.rpow_conj_pdSetLM (β := (1 - α) / (2 * α)) (q := α - 1) hρ hσ
  rwa [hP_sa.star_eq] at key

set_option maxHeartbeats 400000 in
-- heartbeats raised: section-level backward.isDefEq.respectTransparency false increases whnf cost
omit [Nontrivial ℋ] in
lemma quasiVarOpt_eq_quasi_gt {α : ℝ} (hα : 1 < α)
    {ρ σ : L ℋ} (hρ : ρ ∈ pdSetLM (ℋ := ℋ)) (hσ : σ ∈ pdSetLM (ℋ := ℋ)) :
    quasiVar α ρ σ (quasiVarOpt α ρ σ) = sandwichedQuasi α ρ σ := by
  have hρ_pos := (LinearMap.nonneg_iff_isPositive ρ).mp (nonneg_of_pdSetLM hρ)
  have hσ_pos := (LinearMap.nonneg_iff_isPositive σ).mp (nonneg_of_pdSetLM hσ)
  have hσ_unit := isUnit_of_pdSetLM hσ
  have hρ_unit := isUnit_of_pdSetLM hρ
  have hσ_nn := nonneg_of_pdSetLM hσ
  have hρ_nn := nonneg_of_pdSetLM hρ
  unfold quasiVarOpt
  set β' : ℝ := (1 - α) / (2 * α) with hβ'_def
  set P := CFC.rpow σ β' with hP_def
  set Q := CFC.rpow σ (-β') with hQ_def
  set X := P * ρ * P with hX_def
  set H_opt := P * CFC.rpow X (α - 1) * P with hH_opt_def
  have hX_pos : X.IsPositive := _root_.SandwichedRenyiRelativeEntropy.conj_isPositive (_root_.SandwichedRenyiRelativeEntropy.rpow_isSelfAdjoint hσ_pos β') hρ_pos
  have hX_nn : (0 : L ℋ) ≤ X := (LinearMap.nonneg_iff_isPositive X).mpr hX_pos
  have hP_unit : IsUnit P := hσ_unit.cfcRpow β' hσ_nn
  have hX_unit : IsUnit X := (hP_unit.mul hρ_unit).mul hP_unit
  have hPQ : P * Q = 1 := by
    change CFC.rpow σ β' * CFC.rpow σ (-β') = 1
    exact CFC.rpow_mul_rpow_neg β' ⟨hσ_nn, hσ_unit⟩
  have hQP : Q * P = 1 := by
    change CFC.rpow σ (-β') * CFC.rpow σ β' = 1
    exact CFC.rpow_neg_mul_rpow β' ⟨hσ_nn, hσ_unit⟩
  have hY_opt : Q * H_opt * Q = CFC.rpow X (α - 1) := by
    rw [hH_opt_def]
    have : Q * (P * CFC.rpow X (α - 1) * P) * Q =
        (Q * P) * CFC.rpow X (α - 1) * (P * Q) := by simp only [mul_assoc]
    rw [this, hQP, hPQ, one_mul, mul_one]
  have hα_sub_pos : (0 : ℝ) < α - 1 := by linarith
  have hα_pos : (0 : ℝ) < α := by linarith
  have hYq_eq : CFC.rpow (CFC.rpow X (α - 1)) (α / (α - 1)) = CFC.rpow X α := by
    simp only [CFC.rpow_eq_pow]
    set s : NNReal := ⟨α - 1, by linarith⟩
    set t : NNReal := ⟨α / (α - 1), le_of_lt (div_pos hα_pos hα_sub_pos)⟩
    set r : NNReal := ⟨α, by linarith⟩
    have hs0 : (0 : NNReal) < s := by exact_mod_cast hα_sub_pos
    have ht0 : (0 : NNReal) < t := by exact_mod_cast div_pos hα_pos hα_sub_pos
    have hr0 : (0 : NNReal) < r := by exact_mod_cast hα_pos
    have hst : s * t = r := by
      ext; change (α - 1) * (α / (α - 1)) = α
      rw [mul_comm]; exact div_mul_cancel₀ α (by linarith : (α - 1 : ℝ) ≠ 0)
    change (X ^ (↑s : ℝ)) ^ (↑t : ℝ) = X ^ (↑r : ℝ)
    rw [← CFC.nnrpow_eq_rpow hs0, ← CFC.nnrpow_eq_rpow ht0,
        ← CFC.nnrpow_eq_rpow hr0, CFC.nnrpow_nnrpow, hst]
  have hXX_eq : X * CFC.rpow X (α - 1) = CFC.rpow X α := by
    simp only [CFC.rpow_eq_pow]
    set s : NNReal := ⟨α - 1, by linarith⟩
    set r : NNReal := ⟨α, by linarith⟩
    have hs0 : (0 : NNReal) < s := by exact_mod_cast hα_sub_pos
    have hr0 : (0 : NNReal) < r := by exact_mod_cast hα_pos
    have h1s : (1 : NNReal) + s = r := by ext; change (1 : ℝ) + (α - 1) = α; ring
    change X * X ^ (↑s : ℝ) = X ^ (↑r : ℝ)
    conv_lhs => lhs; rw [show X = X ^ (1 : NNReal) from by
      rw [CFC.nnrpow_eq_rpow one_pos, NNReal.coe_one]; exact (CFC.rpow_one X hX_nn).symm]
    rw [← CFC.nnrpow_eq_rpow hs0, ← CFC.nnrpow_eq_rpow hr0,
        ← CFC.nnrpow_add one_pos hs0, h1s]
  have hTr_Hρ : Tr (H_opt * ρ) = Tr (X * CFC.rpow X (α - 1)) := by
    rw [hH_opt_def]
    have : Tr (P * CFC.rpow X (α - 1) * P * ρ) =
        Tr (P * ρ * P * CFC.rpow X (α - 1)) := by
      calc Tr (P * CFC.rpow X (α - 1) * P * ρ)
          = Tr (ρ * (P * CFC.rpow X (α - 1) * P)) := (_root_.SandwichedRenyiRelativeEntropy.trace_mul_comm _ _).symm
        _ = Tr (ρ * P * (CFC.rpow X (α - 1) * P)) := by simp only [mul_assoc]
        _ = Tr ((CFC.rpow X (α - 1) * P) * (ρ * P)) := _root_.SandwichedRenyiRelativeEntropy.trace_mul_comm _ _
        _ = Tr (CFC.rpow X (α - 1) * (P * (ρ * P))) := by simp only [mul_assoc]
        _ = Tr (P * (ρ * P) * CFC.rpow X (α - 1)) := (_root_.SandwichedRenyiRelativeEntropy.trace_mul_comm _ _).symm
        _ = Tr (P * ρ * P * CFC.rpow X (α - 1)) := by simp only [mul_assoc]
    rw [this, hX_def]
  have hexp : (α - 1 : ℝ) / (2 * α) = -β' := by rw [hβ'_def]; ring
  unfold quasiVar sandwichedQuasi
  rw [hexp, hY_opt, hYq_eq, hTr_Hρ, hXX_eq]
  set T := Tr (CFC.rpow X α)
  push_cast; ring

omit [Nontrivial ℋ] in
set_option backward.isDefEq.respectTransparency false in
 lemma quasiVarOpt_eq_quasi_lt {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {ρ σ : L ℋ} (hρ : ρ ∈ pdSetLM (ℋ := ℋ)) (hσ : σ ∈ pdSetLM (ℋ := ℋ)) :
    quasiVar α ρ σ (quasiVarOpt α ρ σ) = sandwichedQuasi α ρ σ := by
  have hρ_pos := (LinearMap.nonneg_iff_isPositive ρ).mp (nonneg_of_pdSetLM hρ)
  have hσ_pos := (LinearMap.nonneg_iff_isPositive σ).mp (nonneg_of_pdSetLM hσ)
  have hσ_unit := isUnit_of_pdSetLM hσ
  have hρ_unit := isUnit_of_pdSetLM hρ
  have hσ_nn := nonneg_of_pdSetLM hσ
  have hρ_nn := nonneg_of_pdSetLM hρ
  unfold quasiVarOpt
  set β' : ℝ := (1 - α) / (2 * α) with hβ'_def
  set P := CFC.rpow σ β' with hP_def
  set Q := CFC.rpow σ (-β') with hQ_def
  set X := P * ρ * P with hX_def
  set H_opt := P * CFC.rpow X (α - 1) * P with hH_opt_def
  have hX_pos : X.IsPositive := _root_.SandwichedRenyiRelativeEntropy.conj_isPositive (_root_.SandwichedRenyiRelativeEntropy.rpow_isSelfAdjoint hσ_pos β') hρ_pos
  have hX_nn : (0 : L ℋ) ≤ X := (LinearMap.nonneg_iff_isPositive X).mpr hX_pos
  have hP_unit : IsUnit P := hσ_unit.cfcRpow β' hσ_nn
  have hX_unit : IsUnit X := (hP_unit.mul hρ_unit).mul hP_unit
  have hPQ : P * Q = 1 := by
    change CFC.rpow σ β' * CFC.rpow σ (-β') = 1
    exact CFC.rpow_mul_rpow_neg β' ⟨hσ_nn, hσ_unit⟩
  have hQP : Q * P = 1 := by
    change CFC.rpow σ (-β') * CFC.rpow σ β' = 1
    exact CFC.rpow_neg_mul_rpow β' ⟨hσ_nn, hσ_unit⟩
  have hY_opt : Q * H_opt * Q = CFC.rpow X (α - 1) := by
    rw [hH_opt_def]
    have : Q * (P * CFC.rpow X (α - 1) * P) * Q =
        (Q * P) * CFC.rpow X (α - 1) * (P * Q) := by simp only [mul_assoc]
    rw [this, hQP, hPQ, one_mul, mul_one]
  have hα_sub_neg : (α - 1 : ℝ) < 0 := by linarith
  have hα_sub_ne : (α - 1 : ℝ) ≠ 0 := ne_of_lt hα_sub_neg
  have hα_pos : (0 : ℝ) < α := hα0
  have hYq_eq : CFC.rpow (CFC.rpow X (α - 1)) (α / (α - 1)) = CFC.rpow X α := by
    simp only [CFC.rpow_eq_pow]
    rw [CFC.rpow_rpow X (α - 1) (α / (α - 1)) hα_sub_ne ⟨hX_nn, hX_unit⟩]
    congr 1
    rw [mul_comm]; exact div_mul_cancel₀ α hα_sub_ne
  have hXX_eq : X * CFC.rpow X (α - 1) = CFC.rpow X α := by
    simp only [CFC.rpow_eq_pow]
    conv_lhs => lhs; rw [show X = X ^ (1 : ℝ) from (CFC.rpow_one X hX_nn).symm]
    rw [← CFC.rpow_add hX_unit]
    congr 1; ring
  have hTr_Hρ : Tr (H_opt * ρ) = Tr (X * CFC.rpow X (α - 1)) := by
    rw [hH_opt_def]
    have : Tr (P * CFC.rpow X (α - 1) * P * ρ) =
        Tr (P * ρ * P * CFC.rpow X (α - 1)) := by
      calc Tr (P * CFC.rpow X (α - 1) * P * ρ)
          = Tr (ρ * (P * CFC.rpow X (α - 1) * P)) := (_root_.SandwichedRenyiRelativeEntropy.trace_mul_comm _ _).symm
        _ = Tr (ρ * P * (CFC.rpow X (α - 1) * P)) := by simp only [mul_assoc]
        _ = Tr ((CFC.rpow X (α - 1) * P) * (ρ * P)) := _root_.SandwichedRenyiRelativeEntropy.trace_mul_comm _ _
        _ = Tr (CFC.rpow X (α - 1) * (P * (ρ * P))) := by simp only [mul_assoc]
        _ = Tr (P * (ρ * P) * CFC.rpow X (α - 1)) := (_root_.SandwichedRenyiRelativeEntropy.trace_mul_comm _ _).symm
        _ = Tr (P * ρ * P * CFC.rpow X (α - 1)) := by simp only [mul_assoc]
    rw [this, hX_def]
  have hexp : (α - 1 : ℝ) / (2 * α) = -β' := by rw [hβ'_def]; ring
  unfold quasiVar sandwichedQuasi
  rw [hexp, hY_opt, hYq_eq, hTr_Hρ, hXX_eq]
  set T := Tr (CFC.rpow X α)
  push_cast; ring

omit [Nontrivial ℋ] in
 lemma isPositive_of_pdSetLM {A : L ℋ} (hA : A ∈ pdSetLM (ℋ := ℋ)) :
    A.IsPositive :=
  (LinearMap.nonneg_iff_isPositive A).mp (nonneg_of_pdSetLM hA)

omit [Nontrivial ℋ] in
lemma trace_H_mul_combo_re (H ρ₁ ρ₂ : L ℋ) (θ : ℝ) :
    (Tr (H * ((1 - θ) • ρ₁ + θ • ρ₂))).re =
    (1 - θ) * (Tr (H * ρ₁)).re + θ * (Tr (H * ρ₂)).re := by
  rw [mul_add, mul_smul_comm, mul_smul_comm]
  exact _root_.SandwichedRenyiRelativeEntropy.trace_re_convex_combo θ (H * ρ₁) (H * ρ₂)

/-- Joint convexity of `(ρ, σ) ↦ Re quasiVar α ρ σ H` on `pdSetLM × pdSetLM` for a fixed
    pd `H` and `α > 1`. The `ρ`-term is linear, the `σ`-term concave with coefficient
    `−(α−1) < 0`. (Used to extend joint convexity to the psd cone in the DPI proof.) -/
theorem quasiVar_re_jointlyConvex_pdSetLM {α : ℝ} (hα : 1 < α)
    {H : L ℋ} (hH : H ∈ pdSetLM (ℋ := ℋ)) :
    JointlyConvexOn (pdSetLM (ℋ := ℋ)) (pdSetLM (ℋ := ℋ))
      (fun ρ σ => (quasiVar α ρ σ H).re) := by
  intro ρ₁ ρ₂ σ₁ σ₂ θ hρ₁ hρ₂ hσ₁ hσ₂ hθ0 hθ1
  simp only [smul_eq_mul]
  have hα0 : (0 : ℝ) < α := by linarith
  have hα_ne1 : α ≠ 1 := ne_of_gt hα
  have hα_ge : (1 : ℝ) / 2 ≤ α := by linarith
  set ρ_c := (1 - θ) • ρ₁ + θ • ρ₂ with hρc_def
  set σ_c := (1 - θ) • σ₁ + θ • σ₂ with hσc_def
  have h_sigma_concave := sigma_term_concaveOn hα0 hα_ne1 hα_ge hH
  have h_sigma_ineq : (1 - θ) * (Tr (CFC.rpow (CFC.rpow σ₁ ((α - 1) / (2 * α)) * H *
          CFC.rpow σ₁ ((α - 1) / (2 * α))) (α / (α - 1)))).re +
      θ * (Tr (CFC.rpow (CFC.rpow σ₂ ((α - 1) / (2 * α)) * H *
          CFC.rpow σ₂ ((α - 1) / (2 * α))) (α / (α - 1)))).re ≤
      (Tr (CFC.rpow (CFC.rpow σ_c ((α - 1) / (2 * α)) * H *
          CFC.rpow σ_c ((α - 1) / (2 * α))) (α / (α - 1)))).re :=
    h_sigma_concave.2 hσ₁ hσ₂ (by linarith : (0 : ℝ) ≤ 1 - θ) hθ0 (by linarith)
  have h_trace_lin : (Tr (H * ρ_c)).re = (1 - θ) * (Tr (H * ρ₁)).re + θ * (Tr (H * ρ₂)).re := by
    change (Tr (H * ((1 - θ) • ρ₁ + θ • ρ₂))).re = _
    exact trace_H_mul_combo_re H ρ₁ ρ₂ θ
  change (quasiVar α ρ_c σ_c H).re ≤
    (1 - θ) * (quasiVar α ρ₁ σ₁ H).re + θ * (quasiVar α ρ₂ σ₂ H).re
  unfold quasiVar
  simp only [Complex.sub_re, Complex.re_ofReal_mul]
  have hα1_pos : (0 : ℝ) < α - 1 := by linarith
  nlinarith [h_trace_lin, h_sigma_ineq]
end JointConvexity
end SandwichedRenyiRelativeEntropy


