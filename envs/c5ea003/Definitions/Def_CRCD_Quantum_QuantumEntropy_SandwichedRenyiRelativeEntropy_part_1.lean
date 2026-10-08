-- Prove2me | Definitions.Def_CRCD_Quantum_QuantumEntropy_SandwichedRenyiRelativeEntropy_part_1
-- name    : CRCD_Quantum_QuantumEntropy_SandwichedRenyiRelativeEntropy_part_1
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-08T00:52:19.158085+00:00
-- url     : https://prove2.me/theorems/335579d7-cf78-4324-85c6-a47a18e45f84
-- title:
--   Sandwiched trace functionals and variational bounds
-- statement:
--   Let $L(H)$ denote the endomorphisms of a finite-dimensional complex Hilbert space. With powers interpreted by the formal continuous functional calculus, define
--   $$
--   Q_\alpha(\rho\Vert\sigma)=\operatorname{Tr}\bigl[(\sigma^{(1-\alpha)/(2\alpha)}\rho\sigma^{(1-\alpha)/(2\alpha)})^\alpha\bigr],\qquad
--   D_\alpha(\rho\Vert\sigma)=\frac{\ln(\operatorname{Re}Q_\alpha(\rho\Vert\sigma)/\operatorname{Re}\operatorname{Tr}\rho)}{\alpha-1},
--   $$
--   and $V_\alpha(\rho,\sigma;X)=\alpha\operatorname{Tr}(X\rho)-(\alpha-1)\operatorname{Tr}[(\sigma^{(\alpha-1)/(2\alpha)}X\sigma^{(\alpha-1)/(2\alpha)})^{\alpha/(\alpha-1)}]$. These are total definitions for real $\alpha$ and arbitrary operators; their entropy interpretation uses positive inputs and admissible orders. $Q_\alpha,V_\alpha$ are complex-valued and $D_\alpha$ is real-valued, trace-normalized and measured in nats, with Lean's total logarithm/division conventions rather than an infinity branch. No trace-one premise is built into them.
--
--   For nonzero $H$, the part defines the positive-definite set $\mathcal P=\{A:A>0\}$ via continuous operators, the star-algebra map to that model, and $L_s(K,A,B)=\operatorname{Re}\operatorname{Tr}(A^sK^*B^{1-s}K)$. It also introduces $T_p(B,A)=\operatorname{Re}\operatorname{Tr}[(B^*A^pB)^{1/p}]$ and $F_p(B,A,X)=L_p(B^*,A,X)-(1-p)\operatorname{Re}\operatorname{Tr}X$.
--
--   For $\rho,\sigma,X\ge0$ and invertible $\sigma$, $V_\alpha\le Q_\alpha$ when $\alpha>1$; when $0<\alpha<1$, $Q_\alpha\le V_\alpha$ additionally requires invertible $X$. On $\mathcal P\times\mathcal P$, $L_s$ is jointly concave for $0<s<1$ and jointly convex for $1\le s\le2$. For every $p<0$, invertible $B$ and $A>0$, $pT_p(B,A)\le F_p(B,A,X)$ for every $X>0$, and equality is attained by some $X>0$. For $0<p\le1$ and $A,X>0$, the reverse inequality holds without an invertibility premise on $B$. Further facts establish convexity and power/conjugation stability of $\mathcal P$, compatibility of real powers with the continuous-operator model, positivity of self-adjoint sandwiches, and cyclic trace cancellation.
-- source:
--   https://github.com/Hayata-Yamasaki-Group/lean-quantum/blob/bf1c4f6aaec84948f1a1c76c0728432813404a0f/Quantum/QuantumEntropy/SandwichedRenyiRelativeEntropy.lean#L27-L835

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

/-- Sandwiched quasi-relative entropy:
    `Q_α(ρ‖σ) = Tr((σ^{(1-α)/(2α)} ρ σ^{(1-α)/(2α)})^α)`. -/
noncomputable def sandwichedQuasi (α : ℝ) (ρ σ : L ℋ) : ℂ :=
  Tr (CFC.rpow (CFC.rpow σ ((1 - α) / (2 * α)) * ρ * CFC.rpow σ ((1 - α) / (2 * α))) α)

/-- The variational functional (equivalent QHQ form):
    `F(H) = α Tr(Hρ) - (α-1) Tr((σ^{(α-1)/(2α)} H σ^{(α-1)/(2α)})^{α/(α-1)})`. -/
noncomputable def quasiVar (α : ℝ) (ρ σ H : L ℋ) : ℂ :=
  (α : ℂ) * Tr (H * ρ)
    - ((α - 1 : ℝ) : ℂ) * Tr (CFC.rpow
        (CFC.rpow σ ((α - 1) / (2 * α)) * H * CFC.rpow σ ((α - 1) / (2 * α)))
        (α / (α - 1)))

/-- Sandwiched Rényi relative entropy for `α ∈ (0,1) ∪ (1,∞)`:
    `D_α(ρ‖σ) = (1/(α-1)) · log(Q_α(ρ‖σ) / Tr ρ)`. -/
noncomputable def sandwichedRenyiDiv (α : ℝ) (ρ σ : L ℋ) : ℝ :=
  (1 / (α - 1)) * Real.log ((sandwichedQuasi α ρ σ).re / (Tr ρ).re)

variable [Nontrivial ℋ]

/-- Strictly positive operators as `QuantumState.L ℋ`, pulled back from the CLM `pdSet`. -/
def pdSetLM : Set (L ℋ) :=
  { A | A.toContinuousLinearMap ∈ pdSet (ℋ := ℋ) }

/-- Lieb trace functional on linear maps, via the continuous-linear model in `LiebAndoTrace`. -/
noncomputable def liebTraceMapLM (s : ℝ) (K A B : L ℋ) : ℝ :=
  liebTraceMap (ℋ := ℋ) s K.toContinuousLinearMap A.toContinuousLinearMap B.toContinuousLinearMap

/-- `toContinuousLinearMap` as a `StarAlgHom`. -/
noncomputable def toCLMStarAlgHom :
    (L ℋ) →⋆ₐ[ℂ] (LownerHeinzTheorem.L ℋ) where
  toFun := LinearMap.toContinuousLinearMap
  map_one' := by ext; rfl
  map_mul' _ _ := by ext; rfl
  map_zero' := by ext; rfl
  map_add' _ _ := by ext; rfl
  commutes' _ := by ext; rfl
  map_star' := by
    intro f
    change f.adjoint.toContinuousLinearMap = star f.toContinuousLinearMap
    rw [LinearMap.adjoint_toContinuousLinearMap, ContinuousLinearMap.star_eq_adjoint]

/-- Trace of the conjugated power `A ↦ Re Tr((B† · A^p · B)^{1/p})`. -/
noncomputable def traceConjPow (p : ℝ) (B A : L ℋ) : ℝ :=
  (Tr (CFC.rpow (star B * CFC.rpow A p * B) (1 / p))).re

/-- Variational (Legendre-type) functional associated to `traceConjPow`:
    `F(A, X) = liebTraceMapLM(p, B†, A, X) − (1−p) · Re Tr X`.
    For `p < 0`: `p · traceConjPow = inf_X F`; for `p > 0`: `p · traceConjPow = sup_X F`. -/
noncomputable def traceConjPowVar (p : ℝ) (B A X : L ℋ) : ℝ :=
  liebTraceMapLM (ℋ := ℋ) p (star B) A X - (1 - p) * (Tr X).re

end Definition

section VariationalRepresentation

universe u

variable {ℋ : Type u} [Qudit ℋ]

set_option linter.style.longLine false

/-- Conjugation by a self-adjoint operator preserves positivity: A * B * A ≥ 0 when A† = A, B ≥ 0. -/
 lemma conj_isPositive {A : L ℋ} (hA : IsSelfAdjoint A) {B : L ℋ} (hB : B.IsPositive) :
    (A * B * A).IsPositive := by
  have hadj : LinearMap.adjoint A = A := by
    rw [← LinearMap.star_eq_adjoint]; exact hA.star_eq
  have h := hB.conj_adjoint A
  rw [hadj] at h
  exact h

/-- Cyclic trace with unit cancellation:
    Tr((P ρ P)(Q H Q)) = Tr(H ρ) when P Q = 1 and Q P = 1. -/
 lemma trace_mul_comm (f g : L ℋ) : Tr (f * g) = Tr (g * f) :=
  LinearMap.trace_comp_comm' g f

 lemma trace_conj_cancel {P Q ρ H : L ℋ}
    (hPQ : P * Q = 1) (hQP : Q * P = 1) :
    Tr ((P * ρ * P) * (Q * H * Q)) = Tr (H * ρ) := by
  have h1 : (P * ρ * P) * (Q * H * Q) = P * (ρ * H) * Q := by
    have : P * (ρ * (P * (Q * (H * Q)))) = P * (ρ * (H * Q)) := by
      congr 2; rw [show P * (Q * (H * Q)) = (P * Q) * (H * Q) from by
        simp only [mul_assoc]]; rw [hPQ, one_mul]
    simp only [mul_assoc] at this ⊢; exact this
  rw [h1]
  rw [show P * (ρ * H) * Q = P * (ρ * H) * Q from rfl]
  rw [_root_.SandwichedRenyiRelativeEntropy.trace_mul_comm (P * (ρ * H)) Q, ← mul_assoc Q P, hQP, one_mul]
  exact (_root_.SandwichedRenyiRelativeEntropy.trace_mul_comm H ρ).symm

/-- rpow self-adjointness for positive operators. -/
 lemma rpow_isSelfAdjoint {σ : L ℋ} (_hσ : σ.IsPositive) (s : ℝ) :
    IsSelfAdjoint (CFC.rpow σ s) :=
  IsSelfAdjoint.of_nonneg CFC.rpow_nonneg

/-- Algebraic rearrangement: from Young's form to variational form.
    If a ≤ b/p + c/q with p, q Hölder conjugates, then p·a - (p-1)·c ≤ b. -/
 lemma young_to_variational {a b c : ℂ} {p q : ℝ}
    (hp : 1 < p) (hpq : p.HolderConjugate q)
    (h : a ≤ b / ↑p + c / ↑q) :
    ↑p * a - ↑(p - 1) * c ≤ b := by
  have hp_pos : (0 : ℝ) < p := by linarith
  have hp_nn : (0 : ℂ) ≤ ↑p := by exact_mod_cast le_of_lt hp_pos
  have hp_ne : (p : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hp_pos
  have hq_ne : (q : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hpq.right_pos
  rw [sub_le_iff_le_add]
  calc ↑p * a
      ≤ ↑p * (b / ↑p + c / ↑q) := mul_le_mul_of_nonneg_left h hp_nn
    _ = b + ↑p * c / ↑q := by rw [mul_add, mul_div_assoc]; congr 1; field_simp
    _ = b + ↑(p - 1) * c := by
        congr 1; rw [show (p - 1 : ℝ) = p - 1 from rfl]
        rw [show q = p / (p - 1) from hpq.conjugate_eq]; push_cast; field_simp

/-- Upper bound on the variational functional for `α > 1`:
    for all positive `H`, `quasiVar α ρ σ H ≤ sandwichedQuasi α ρ σ`.
    Proof by the Young-inequality argument. -/
theorem quasiVar_le_quasi {α : ℝ} (hα : 1 < α) {ρ σ H : L ℋ}
    (hρ : ρ.IsPositive) (hσ : σ.IsPositive) (hH : H.IsPositive)
    (hσ_unit : IsUnit σ) :
    quasiVar α ρ σ H ≤ sandwichedQuasi α ρ σ := by
  -- β' = (1-α)/(2α), P = σ^β', Q = σ^{-β'} = σ^{(α-1)/(2α)}
  set β' : ℝ := (1 - α) / (2 * α) with hβ'_def
  set P := CFC.rpow σ β' with hP_def
  set Q := CFC.rpow σ (-β') with hQ_def
  set X := P * ρ * P with hX_def
  set Y := Q * H * Q with hY_def
  have hσ_nn : (0 : L ℋ) ≤ σ := (LinearMap.nonneg_iff_isPositive σ).mpr hσ
  have hP_sa : IsSelfAdjoint P := _root_.SandwichedRenyiRelativeEntropy.rpow_isSelfAdjoint hσ β'
  have hQ_sa : IsSelfAdjoint Q := _root_.SandwichedRenyiRelativeEntropy.rpow_isSelfAdjoint hσ (-β')
  have hX_pos : X.IsPositive := _root_.SandwichedRenyiRelativeEntropy.conj_isPositive hP_sa hρ
  have hY_pos : Y.IsPositive := _root_.SandwichedRenyiRelativeEntropy.conj_isPositive hQ_sa hH
  -- P * Q = 1 and Q * P = 1
  have hPQ : P * Q = 1 := by
    change CFC.rpow σ β' * CFC.rpow σ (-β') = 1
    exact CFC.rpow_mul_rpow_neg β' ⟨hσ_nn, hσ_unit⟩
  have hQP : Q * P = 1 := by
    change CFC.rpow σ (-β') * CFC.rpow σ β' = 1
    exact CFC.rpow_neg_mul_rpow β' ⟨hσ_nn, hσ_unit⟩
  -- Hölder conjugates: α and α/(α-1)
  set q := α / (α - 1) with hq_def
  have hpq : α.HolderConjugate q := Real.HolderConjugate.conjExponent hα
  -- Young's inequality: Tr(X ∘ₗ Y) ≤ Tr(X^α)/α + Tr(Y^q)/q
  have hYoung := trace_young_inequality hpq X Y hX_pos hY_pos
  -- Tr(X * Y) = Tr(H * ρ) by cyclic trace + cancellation
  have h_xy : Tr (X * Y) = Tr (H * ρ) := _root_.SandwichedRenyiRelativeEntropy.trace_conj_cancel hPQ hQP
  -- Tr(X^α) = sandwichedQuasi α ρ σ (by definition)
  have h_Xα : Tr (CFC.rpow X α) = sandwichedQuasi α ρ σ := rfl
  -- Tr(Y^q) = the QHQ expression (definitional after exponent arithmetic)
  have h_Yq : Tr (CFC.rpow Y q) =
      Tr (CFC.rpow (CFC.rpow σ ((α - 1) / (2 * α)) * H * CFC.rpow σ ((α - 1) / (2 * α))) q) := by
    have hexp : -β' = (α - 1) / (2 * α) := by rw [hβ'_def]; ring
    rw [hY_def, hQ_def, hexp]
  -- Algebraic rearrangement: from Young to the variational form
  unfold quasiVar
  rw [← h_Yq, ← h_xy]
  exact _root_.SandwichedRenyiRelativeEntropy.young_to_variational hα hpq hYoung



/-- Algebraic rearrangement: from reverse Young's form to variational form.
    If b/r + c/s ≤ a with 0 < s < 1 and 1/r + 1/s = 1, then c ≤ s·a - (s-1)·b. -/
 lemma reverse_young_to_variational {a b c : ℂ} {r s : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1)
    (hrs : 1 / r + 1 / s = 1)
    (h : b / ↑r + c / ↑s ≤ a) :
    c ≤ ↑s * a - ↑(s - 1) * b := by
  have hs_nn : (0 : ℂ) ≤ ↑s := by exact_mod_cast le_of_lt hs0
  have hs_ne : (s : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hs0
  have hr_ne : (r : ℂ) ≠ 0 := by
    suffices r ≠ 0 by exact_mod_cast this
    intro hr0; simp [hr0] at hrs; linarith [one_div_pos.mpr hs0]
  rw [le_sub_iff_add_le, add_comm]
  have key : ↑(s - 1) * b + c = ↑s * (b / ↑r + c / ↑s) := by
    have h_sr : (s - 1 : ℝ) = s / r := by
      have h1 : 1 / r = 1 - 1 / s := by linarith
      field_simp at h1 ⊢; linarith
    have h_cast : (↑(s - 1) : ℂ) = ↑s / ↑r := by
      rw [h_sr]; push_cast; ring
    rw [h_cast]; field_simp
  rw [key]
  exact mul_le_mul_of_nonneg_left h hs_nn

/-- Lower bound on the variational functional for `0 < α < 1`:
    for all invertible positive `H`, `sandwichedQuasi α ρ σ ≤ quasiVar α ρ σ H`.
    Proof by the reverse Young inequality. -/
theorem quasi_le_quasiVar {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {ρ σ H : L ℋ}
    (hρ : ρ.IsPositive) (hσ : σ.IsPositive) (hH : H.IsPositive)
    (hσ_unit : IsUnit σ) (hH_unit : IsUnit H) :
    sandwichedQuasi α ρ σ ≤ quasiVar α ρ σ H := by
  set β' : ℝ := (1 - α) / (2 * α) with hβ'_def
  set P := CFC.rpow σ β' with hP_def
  set Q := CFC.rpow σ (-β') with hQ_def
  set X := P * ρ * P with hX_def
  set Y := Q * H * Q with hY_def
  have hσ_nn : (0 : L ℋ) ≤ σ := (LinearMap.nonneg_iff_isPositive σ).mpr hσ
  have hP_sa : IsSelfAdjoint P := _root_.SandwichedRenyiRelativeEntropy.rpow_isSelfAdjoint hσ β'
  have hQ_sa : IsSelfAdjoint Q := _root_.SandwichedRenyiRelativeEntropy.rpow_isSelfAdjoint hσ (-β')
  have hX_pos : X.IsPositive := _root_.SandwichedRenyiRelativeEntropy.conj_isPositive hP_sa hρ
  have hY_pos : Y.IsPositive := _root_.SandwichedRenyiRelativeEntropy.conj_isPositive hQ_sa hH
  have hPQ : P * Q = 1 := by
    change CFC.rpow σ β' * CFC.rpow σ (-β') = 1
    exact CFC.rpow_mul_rpow_neg β' ⟨hσ_nn, hσ_unit⟩
  have hQP : Q * P = 1 := by
    change CFC.rpow σ (-β') * CFC.rpow σ β' = 1
    exact CFC.rpow_neg_mul_rpow β' ⟨hσ_nn, hσ_unit⟩
  have hQ_unit : IsUnit Q := hσ_unit.cfcRpow (-β') hσ_nn
  have hY_unit : IsUnit Y := (hQ_unit.mul hH_unit).mul hQ_unit
  set r := α / (α - 1) with hr_def
  have hr_neg : r < 0 := by rw [hr_def]; exact div_neg_of_pos_of_neg hα0 (by linarith)
  have hrs : 1 / r + 1 / α = 1 := by
    rw [hr_def]; field_simp; ring
  have hRevYoung := _root_.trace_reverse_young_inequality hr_neg hα0 hα1 hrs Y X
    hY_pos hY_unit hX_pos
  have h_yx : Tr (Y * X) = Tr (H * ρ) := by
    rw [_root_.SandwichedRenyiRelativeEntropy.trace_mul_comm Y X]; exact _root_.SandwichedRenyiRelativeEntropy.trace_conj_cancel hPQ hQP
  have h_Yr : Tr (CFC.rpow Y r) =
      Tr (CFC.rpow (CFC.rpow σ ((α - 1) / (2 * α)) * H * CFC.rpow σ ((α - 1) / (2 * α))) r) := by
    have hexp : -β' = (α - 1) / (2 * α) := by rw [hβ'_def]; ring
    rw [hY_def, hQ_def, hexp]
  unfold quasiVar
  rw [← h_Yr, ← h_yx]
  exact _root_.SandwichedRenyiRelativeEntropy.reverse_young_to_variational hα0 hα1 hrs hRevYoung



end VariationalRepresentation

section LiebAndoLinearMap

open LiebAndoTrace GeneralizedPerspectiveFunction

universe u'

variable {ℋ : Type u'} [Qudit ℋ]
variable [Nontrivial ℋ]

omit [Nontrivial ℋ] in
 lemma toContinuousLinearMap_convex_combo (A₁ A₂ : L ℋ) (θ : ℝ) :
    ((1 - θ) • A₁ + θ • A₂).toContinuousLinearMap =
      (1 - θ) • A₁.toContinuousLinearMap + θ • A₂.toContinuousLinearMap := by
  ext x; rfl

/-- Joint concavity of `liebTraceMapLM` on `pdSetLM`, from `liebTrace_jointlyConcaveOn_pdSet`. -/
theorem liebTrace_jointlyConcaveOn_pdSet_lm {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (K : L ℋ) :
    JointlyConcaveOn (pdSetLM (ℋ := ℋ)) (pdSetLM (ℋ := ℋ)) (liebTraceMapLM (ℋ := ℋ) s K) := by
  intro A₁ A₂ B₁ B₂ θ hA₁ hA₂ hB₁ hB₂ hθ0 hθ1
  dsimp [pdSetLM, liebTraceMapLM] at hA₁ hA₂ hB₁ hB₂ ⊢
  have h :=
    liebTrace_jointlyConcaveOn_pdSet (ℋ := ℋ) hs0 hs1 K.toContinuousLinearMap
      (A₁ := A₁.toContinuousLinearMap) (A₂ := A₂.toContinuousLinearMap)
      (B₁ := B₁.toContinuousLinearMap) (B₂ := B₂.toContinuousLinearMap) (θ := θ)
      hA₁ hA₂ hB₁ hB₂ hθ0 hθ1
  simpa [liebTraceMapLM, _root_.SandwichedRenyiRelativeEntropy.toContinuousLinearMap_convex_combo, smul_eq_mul, sub_eq_add_neg,
    add_comm, add_left_comm, add_assoc] using h

/-- Joint convexity of `liebTraceMapLM` on `pdSetLM`, from `liebTrace_jointlyConvexOn_pdSet`. -/
theorem liebTrace_jointlyConvexOn_pdSet_lm {s : ℝ} (hs1 : 1 ≤ s) (hs2 : s ≤ 2) (K : L ℋ) :
    JointlyConvexOn (pdSetLM (ℋ := ℋ)) (pdSetLM (ℋ := ℋ)) (liebTraceMapLM (ℋ := ℋ) s K) := by
  intro A₁ A₂ B₁ B₂ θ hA₁ hA₂ hB₁ hB₂ hθ0 hθ1
  dsimp [pdSetLM, liebTraceMapLM] at hA₁ hA₂ hB₁ hB₂ ⊢
  have h :=
    liebTrace_jointlyConvexOn_pdSet (ℋ := ℋ) hs1 hs2 K.toContinuousLinearMap
      (A₁ := A₁.toContinuousLinearMap) (A₂ := A₂.toContinuousLinearMap)
      (B₁ := B₁.toContinuousLinearMap) (B₂ := B₂.toContinuousLinearMap) (θ := θ)
      hA₁ hA₂ hB₁ hB₂ hθ0 hθ1
  simpa [liebTraceMapLM, _root_.SandwichedRenyiRelativeEntropy.toContinuousLinearMap_convex_combo, smul_eq_mul, sub_eq_add_neg,
    add_comm, add_left_comm, add_assoc] using h

/-- Convex combinations stay in `pdSetLM` (from the CLM `pdSet_convexCombo`). -/
theorem pdSetLM_convexCombo {A₁ A₂ : L ℋ} (hA₁ : A₁ ∈ pdSetLM (ℋ := ℋ))
    (hA₂ : A₂ ∈ pdSetLM (ℋ := ℋ)) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    (1 - θ) • A₁ + θ • A₂ ∈ pdSetLM (ℋ := ℋ) := by
  dsimp [pdSetLM] at hA₁ hA₂ ⊢
  rw [_root_.SandwichedRenyiRelativeEntropy.toContinuousLinearMap_convex_combo]
  exact pdSet_convexCombo (ℋ := ℋ) hA₁ hA₂ hθ0 hθ1

end LiebAndoLinearMap

section TraceConjPowConcavity

open LiebAndoTrace GeneralizedPerspectiveFunction

universe u''

variable {ℋ : Type u''} [Qudit ℋ] [Nontrivial ℋ]

set_option linter.style.longLine false

/-- `pdSetLM` is convex. -/
 lemma pdSetLM_convex : Convex ℝ (pdSetLM (ℋ := ℋ)) := by
  intro x hx y hy a b ha hb hab
  rw [show a = 1 - b from by linarith]
  exact pdSetLM_convexCombo hx hy hb (by linarith)

omit [Nontrivial ℋ] in
 lemma star_toCLM (f : L ℋ) :
    (star f).toContinuousLinearMap = star (f.toContinuousLinearMap) := by
  change f.adjoint.toContinuousLinearMap = star f.toContinuousLinearMap
  rw [LinearMap.adjoint_toContinuousLinearMap, ContinuousLinearMap.star_eq_adjoint]

omit [Nontrivial ℋ] in
lemma nonneg_of_pdSetLM {A : L ℋ} (hA : A ∈ pdSetLM (ℋ := ℋ)) : (0 : L ℋ) ≤ A := by
  have h_clm_nn : (0 : LownerHeinzTheorem.L ℋ) ≤ A.toContinuousLinearMap := by
    obtain ⟨hA_sa, hA_spec⟩ := hA
    exact (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) _ (ha := hA_sa)).2
      (fun r hr => (hA_spec hr).le)
  rw [LinearMap.nonneg_iff_isPositive]
  have h := (ContinuousLinearMap.nonneg_iff_isPositive _).mp h_clm_nn
  exact ⟨fun x y => h.1 x y, fun x => h.2 x⟩

omit [Nontrivial ℋ] in
 lemma isUnit_toCLM_of_isUnit {A : L ℋ} (h : IsUnit A.toContinuousLinearMap) :
    IsUnit A := by
  obtain ⟨u, hu⟩ := h
  let B := (u⁻¹ : (LownerHeinzTheorem.L ℋ)ˣ).val.toLinearMap
  have h1 : A * B = 1 := by
    ext x
    have h := ContinuousLinearMap.ext_iff.mp u.val_inv x
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply] at h
    rw [hu] at h
    exact h
  have h2 : B * A = 1 := by
    ext x
    have h := ContinuousLinearMap.ext_iff.mp u.inv_val x
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply] at h
    rw [hu] at h
    exact h
  exact ⟨⟨A, B, h1, h2⟩, rfl⟩

omit [Nontrivial ℋ] in
lemma isUnit_of_pdSetLM {A : L ℋ} (hA : A ∈ pdSetLM (ℋ := ℋ)) : IsUnit A := by
  obtain ⟨hA_sa, hA_spec⟩ := hA
  have h0 : (0 : ℝ) ∉ spectrum ℝ A.toContinuousLinearMap := by
    intro h; exact absurd (Set.mem_Ioi.mp (hA_spec h)) (lt_irrefl 0)
  exact _root_.SandwichedRenyiRelativeEntropy.isUnit_toCLM_of_isUnit
    ((spectrum.zero_notMem_iff (R := ℝ) (A := LownerHeinzTheorem.L ℋ)).mp h0)

omit [Nontrivial ℋ] in
lemma pdSetLM_conj {A B : L ℋ} (hA : A ∈ pdSetLM (ℋ := ℋ)) (hB : IsUnit B) :
    star B * A * B ∈ pdSetLM (ℋ := ℋ) := by
  obtain ⟨hA_sa, hA_spec⟩ := hA
  have hA_nn_clm : (0 : LownerHeinzTheorem.L ℋ) ≤ A.toContinuousLinearMap := by
    exact (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) _ (ha := hA_sa)).2
      (fun r hr => (hA_spec hr).le)
  have h_prod_clm : (star B * A * B).toContinuousLinearMap =
      star B.toContinuousLinearMap * A.toContinuousLinearMap * B.toContinuousLinearMap := by
    ext v; rfl
  have hM_nn_clm : (0 : LownerHeinzTheorem.L ℋ) ≤
      star B.toContinuousLinearMap * A.toContinuousLinearMap * B.toContinuousLinearMap :=
    star_left_conjugate_nonneg hA_nn_clm _
  have hB_clm_unit : IsUnit B.toContinuousLinearMap :=
    (toCLMStarAlgHom (ℋ := ℋ)).toRingHom.isUnit_map hB
  have hA_clm_unit : IsUnit A.toContinuousLinearMap :=
    (toCLMStarAlgHom (ℋ := ℋ)).toRingHom.isUnit_map (isUnit_of_pdSetLM ⟨hA_sa, hA_spec⟩)
  have hM_clm_unit : IsUnit (star B.toContinuousLinearMap * A.toContinuousLinearMap *
      B.toContinuousLinearMap) :=
    (hB_clm_unit.star.mul hA_clm_unit).mul hB_clm_unit
  have hM_sa : IsSelfAdjoint (star B.toContinuousLinearMap * A.toContinuousLinearMap *
      B.toContinuousLinearMap) := IsSelfAdjoint.of_nonneg hM_nn_clm
  constructor
  · rw [h_prod_clm]; exact hM_sa
  · rw [h_prod_clm]
    intro r hr
    have h_nn : (0 : ℝ) ≤ r := by
      have h_spec_nn : spectrum ℝ (star B.toContinuousLinearMap *
          A.toContinuousLinearMap * B.toContinuousLinearMap) ⊆ Set.Ici 0 :=
        (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) _ (ha := hM_sa)).1 hM_nn_clm
      simpa [Set.Ici] using h_spec_nn hr
    rcases lt_or_eq_of_le h_nn with h | h
    · exact h
    · exfalso
      rw [← h] at hr
      exact (spectrum.zero_notMem_iff (R := ℝ)).mpr hM_clm_unit hr

omit [Nontrivial ℋ] in
lemma pdSetLM_rpow_ne {A : L ℋ} (hA : A ∈ pdSetLM (ℋ := ℋ)) {p : ℝ} :
    CFC.rpow A p ∈ pdSetLM (ℋ := ℋ) := by
  have hA_nn := nonneg_of_pdSetLM hA
  have hA_unit := isUnit_of_pdSetLM hA
  have hAp_nn : (0 : L ℋ) ≤ CFC.rpow A p := CFC.rpow_nonneg
  have hAp_unit : IsUnit (CFC.rpow A p) := hA_unit.cfcRpow p hA_nn
  have hAp_sa : IsSelfAdjoint (CFC.rpow A p) := IsSelfAdjoint.of_nonneg hAp_nn
  have hAp_clm_nn : (0 : LownerHeinzTheorem.L ℋ) ≤
      (CFC.rpow A p).toContinuousLinearMap := by
    change (0 : LownerHeinzTheorem.L ℋ) ≤ (toCLMStarAlgHom (ℋ := ℋ)) (CFC.rpow A p)
    exact map_nonneg (toCLMStarAlgHom (ℋ := ℋ)) hAp_nn
  have hAp_clm_unit : IsUnit (CFC.rpow A p).toContinuousLinearMap := by
    change IsUnit ((toCLMStarAlgHom (ℋ := ℋ)) (CFC.rpow A p))
    exact (toCLMStarAlgHom (ℋ := ℋ)).toRingHom.isUnit_map hAp_unit
  have hAp_clm_sa : IsSelfAdjoint (CFC.rpow A p).toContinuousLinearMap :=
    IsSelfAdjoint.of_nonneg hAp_clm_nn
  refine ⟨hAp_clm_sa, ?_⟩
  intro r hr
  have h_spec_nn : spectrum ℝ (CFC.rpow A p).toContinuousLinearMap ⊆ Set.Ici 0 :=
    (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) _ (ha := hAp_clm_sa)).1 hAp_clm_nn
  rcases lt_or_eq_of_le (by simpa [Set.Ici] using h_spec_nn hr) with h | h
  · exact h
  · exfalso; rw [← h] at hr
    exact (spectrum.zero_notMem_iff (R := ℝ)).mpr hAp_clm_unit hr

omit [Nontrivial ℋ] in
 lemma pdSetLM_rpow {A : L ℋ} (hA : A ∈ pdSetLM (ℋ := ℋ)) {p : ℝ} :
    CFC.rpow A p ∈ pdSetLM (ℋ := ℋ) :=
  pdSetLM_rpow_ne hA

omit [Nontrivial ℋ] in
set_option backward.isDefEq.respectTransparency false in
 lemma rpow_toCLM {A : L ℋ} {p : ℝ} (hp : 0 ≤ p)
    (hA : (0 : L ℋ) ≤ A) :
    (CFC.rpow A p).toContinuousLinearMap = CFC.rpow A.toContinuousLinearMap p := by
  have hA_sa : IsSelfAdjoint A := IsSelfAdjoint.of_nonneg hA
  have hφ_nn : (0 : LownerHeinzTheorem.L ℋ) ≤ A.toContinuousLinearMap :=
    map_nonneg (toCLMStarAlgHom (ℋ := ℋ)) hA
  have hφ_sa : IsSelfAdjoint A.toContinuousLinearMap :=
    IsSelfAdjoint.map hA_sa (toCLMStarAlgHom (ℋ := ℋ))
  have hcont : Continuous (toCLMStarAlgHom (ℋ := ℋ)) :=
    (toCLMStarAlgHom (ℋ := ℋ)).toAlgHom.toLinearMap.continuous_of_finiteDimensional
  have hf : ContinuousOn (fun x : ℝ => x ^ p) (spectrum ℝ A) :=
    (Real.continuous_rpow_const hp).continuousOn
  rw [CFC.rpow_eq_pow, CFC.rpow_eq_pow]
  rw [CFC.rpow_eq_cfc_real (a := A) (ha := hA)]
  rw [CFC.rpow_eq_cfc_real (a := A.toContinuousLinearMap) (ha := hφ_nn)]
  exact StarAlgHomClass.map_cfc (R := ℝ) (S := ℂ)
    (toCLMStarAlgHom (ℋ := ℋ)) (fun x : ℝ => x ^ p) A
    (hf := hf) (hφ := hcont) (ha := hA_sa) (hφa := hφ_sa)

omit [Nontrivial ℋ] in
set_option backward.isDefEq.respectTransparency false in
 lemma rpow_toCLM_pd {A : L ℋ} {p : ℝ}
    (hA : A ∈ pdSetLM (ℋ := ℋ)) :
    (CFC.rpow A p).toContinuousLinearMap = CFC.rpow A.toContinuousLinearMap p := by
  have hA_nn := nonneg_of_pdSetLM hA
  by_cases hp : 0 ≤ p
  · exact _root_.SandwichedRenyiRelativeEntropy.rpow_toCLM hp hA_nn
  · push_neg at hp
    obtain ⟨hA_sa_clm, hA_spec⟩ := hA
    have hA_sa : IsSelfAdjoint A := IsSelfAdjoint.of_nonneg hA_nn
    have hφ_nn : (0 : LownerHeinzTheorem.L ℋ) ≤ A.toContinuousLinearMap :=
      map_nonneg (toCLMStarAlgHom (ℋ := ℋ)) hA_nn
    have hφ_sa : IsSelfAdjoint A.toContinuousLinearMap :=
      IsSelfAdjoint.map hA_sa (toCLMStarAlgHom (ℋ := ℋ))
    have hcont : Continuous (toCLMStarAlgHom (ℋ := ℋ)) :=
      (toCLMStarAlgHom (ℋ := ℋ)).toAlgHom.toLinearMap.continuous_of_finiteDimensional
    have hA_unit := isUnit_of_pdSetLM ⟨hA_sa_clm, hA_spec⟩
    have h_spec_lm_nn : spectrum ℝ A ⊆ Set.Ici 0 :=
      (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) _ (ha := hA_sa)).1 hA_nn
    have h0_not_mem : (0 : ℝ) ∉ spectrum ℝ A :=
      (spectrum.zero_notMem_iff (R := ℝ) (A := L ℋ)).mpr hA_unit
    have hf : ContinuousOn (fun x : ℝ => x ^ p) (spectrum ℝ A) :=
      ContinuousOn.rpow_const continuousOn_id fun x hx =>
        Or.inl (ne_of_gt (lt_of_le_of_ne
          (by simpa [Set.Ici] using h_spec_lm_nn hx)
          (fun h => h0_not_mem (h ▸ hx))))
    rw [CFC.rpow_eq_pow, CFC.rpow_eq_pow]
    rw [CFC.rpow_eq_cfc_real (a := A) (ha := hA_nn)]
    rw [CFC.rpow_eq_cfc_real (a := A.toContinuousLinearMap) (ha := hφ_nn)]
    exact StarAlgHomClass.map_cfc (R := ℝ) (S := ℂ)
      (toCLMStarAlgHom (ℋ := ℋ)) (fun x : ℝ => x ^ p) A
      (hf := hf) (hφ := hcont) (ha := hA_sa) (hφa := hφ_sa)

omit [Nontrivial ℋ] in
set_option backward.isDefEq.respectTransparency false in
 lemma liebTraceMapLM_as_lm_trace_pd {p : ℝ}
    (B A X : L ℋ)
    (hA : A ∈ pdSetLM (ℋ := ℋ)) (hX : X ∈ pdSetLM (ℋ := ℋ))
    (h1p : 0 ≤ 1 - p) :
    liebTraceMapLM (ℋ := ℋ) p (star B) A X =
      (Tr (star B * CFC.rpow A p * B * CFC.rpow X (1 - p))).re := by
  have hX_nn := nonneg_of_pdSetLM hX
  unfold liebTraceMapLM liebTraceMap
  simp only [_root_.SandwichedRenyiRelativeEntropy.star_toCLM, star_star]
  have h1 : A.toContinuousLinearMap ^ p = (CFC.rpow A p).toContinuousLinearMap :=
    (_root_.SandwichedRenyiRelativeEntropy.rpow_toCLM_pd hA).symm
  have h2 : X.toContinuousLinearMap ^ (1 - p) = (CFC.rpow X (1 - p)).toContinuousLinearMap :=
    (_root_.SandwichedRenyiRelativeEntropy.rpow_toCLM h1p hX_nn).symm
  have h3 : star (B.toContinuousLinearMap) = (star B).toContinuousLinearMap :=
    (_root_.SandwichedRenyiRelativeEntropy.star_toCLM B).symm
  rw [h1, h2, h3]
  simp only [traceRe]
  have h_prod : ((CFC.rpow A p).toContinuousLinearMap * B.toContinuousLinearMap *
      (CFC.rpow X (1 - p)).toContinuousLinearMap *
      (star B).toContinuousLinearMap).toLinearMap =
    CFC.rpow A p * B * CFC.rpow X (1 - p) * star B := by ext v; rfl
  rw [h_prod]
  congr 1
  rw [_root_.SandwichedRenyiRelativeEntropy.trace_mul_comm (CFC.rpow A p * B * CFC.rpow X (1 - p)) (star B)]
  simp only [mul_assoc]

omit [Nontrivial ℋ] in
set_option backward.isDefEq.respectTransparency false in
 lemma liebTraceMapLM_as_lm_trace {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (B A X : L ℋ) (hA : (0 : L ℋ) ≤ A) (hX : (0 : L ℋ) ≤ X) :
    liebTraceMapLM (ℋ := ℋ) p (star B) A X =
      (Tr (star B * CFC.rpow A p * B * CFC.rpow X (1 - p))).re := by
  unfold liebTraceMapLM liebTraceMap
  simp only [_root_.SandwichedRenyiRelativeEntropy.star_toCLM, star_star]
  have h1 : A.toContinuousLinearMap ^ p = (CFC.rpow A p).toContinuousLinearMap :=
    (_root_.SandwichedRenyiRelativeEntropy.rpow_toCLM hp0 hA).symm
  have h2 : X.toContinuousLinearMap ^ (1 - p) = (CFC.rpow X (1 - p)).toContinuousLinearMap :=
    (_root_.SandwichedRenyiRelativeEntropy.rpow_toCLM (by linarith) hX).symm
  have h3 : star (B.toContinuousLinearMap) = (star B).toContinuousLinearMap :=
    (_root_.SandwichedRenyiRelativeEntropy.star_toCLM B).symm
  rw [h1, h2, h3]
  simp only [traceRe]
  have h_prod : ((CFC.rpow A p).toContinuousLinearMap * B.toContinuousLinearMap *
      (CFC.rpow X (1 - p)).toContinuousLinearMap *
      (star B).toContinuousLinearMap).toLinearMap =
    CFC.rpow A p * B * CFC.rpow X (1 - p) * star B := by ext v; rfl
  rw [h_prod]
  congr 1
  rw [_root_.SandwichedRenyiRelativeEntropy.trace_mul_comm (CFC.rpow A p * B * CFC.rpow X (1 - p)) (star B)]
  simp only [mul_assoc]

omit [Nontrivial ℋ] in
set_option backward.isDefEq.respectTransparency false in
/-- Variational inequality (−1 ≤ p < 0):
    ∀ X ∈ pdSetLM, p · traceConjPow(p,B,A) ≤ F(A,X).
    Follows from the reverse trace Young inequality with M = B†A^pB. -/
 lemma traceConjPowVar_le_neg {p : ℝ} (hp0 : p < 0)
    {B A X : L ℋ} (hB : IsUnit B) (hA : A ∈ pdSetLM (ℋ := ℋ)) (hX : X ∈ pdSetLM (ℋ := ℋ)) :
    p * traceConjPow (ℋ := ℋ) p B A ≤ traceConjPowVar (ℋ := ℋ) p B A X := by
  have hA_nn := nonneg_of_pdSetLM hA
  have hX_nn := nonneg_of_pdSetLM hX
  have hpne : (p : ℝ) ≠ 0 := ne_of_lt hp0
  set M := star B * CFC.rpow A p * B with hM_def
  set N := CFC.rpow X (1 - p) with hN_def
  have hApd : CFC.rpow A p ∈ pdSetLM (ℋ := ℋ) := pdSetLM_rpow_ne hA
  have hMpd : M ∈ pdSetLM (ℋ := ℋ) := pdSetLM_conj hApd hB
  have hM_unit : IsUnit M := isUnit_of_pdSetLM hMpd
  have hM_nn : (0 : L ℋ) ≤ M := star_left_conjugate_nonneg CFC.rpow_nonneg _
  have hN_nn : (0 : L ℋ) ≤ N := CFC.rpow_nonneg
  have hM_pos : M.IsPositive := (LinearMap.nonneg_iff_isPositive _).mp hM_nn
  have hN_pos : N.IsPositive := (LinearMap.nonneg_iff_isPositive _).mp hN_nn
  have h1_sub_p_pos : 0 < 1 - p := by linarith
  have h_bridge := _root_.SandwichedRenyiRelativeEntropy.liebTraceMapLM_as_lm_trace_pd B A X hA hX (by linarith)
  set r := 1 / p with hr_def
  set s := 1 / (1 - p) with hs_def
  have hr_neg : r < 0 := by rw [hr_def]; exact div_neg_of_pos_of_neg one_pos hp0
  have hs_pos : 0 < s := by rw [hs_def]; positivity
  have hs_lt_1 : s < 1 := by
    rw [hs_def]; rw [div_lt_one h1_sub_p_pos]; linarith
  have hrs : 1 / r + 1 / s = 1 := by
    rw [hr_def, hs_def]; field_simp; ring
  have hMr : CFC.rpow M r = CFC.rpow (star B * CFC.rpow A p * B) (1 / p) := by
    rw [hM_def]
  have hNs : CFC.rpow N s = X := by
    rw [hN_def, hs_def, CFC.rpow_eq_pow, CFC.rpow_eq_pow]
    rw [CFC.rpow_rpow_of_exponent_nonneg X (1 - p) (1 / (1 - p))
      (by linarith) (by positivity)]
    rw [show (1 - p) * (1 / (1 - p)) = 1 from by field_simp]
    exact CFC.rpow_one X hX_nn
  have hRevYoung := _root_.trace_reverse_young_inequality hr_neg hs_pos hs_lt_1 hrs M N
    hM_pos hM_unit hN_pos
  have hRevYoung_re : (Tr (CFC.rpow M r) / ↑r + Tr (CFC.rpow N s) / ↑s).re ≤
      (Tr (M ∘ₗ N)).re :=
    (RCLike.le_iff_re_im.mp hRevYoung).1
  rw [Complex.add_re, Complex.div_ofReal_re, Complex.div_ofReal_re, hNs] at hRevYoung_re
  have hMN_eq : (Tr (M ∘ₗ N)).re = (Tr (M * N)).re := rfl
  rw [hMN_eq] at hRevYoung_re
  have hr_eq : (Tr (CFC.rpow M r)).re / r = p * (Tr (CFC.rpow M r)).re := by
    rw [hr_def]; field_simp
  have hs_eq : (Tr X).re / s = (1 - p) * (Tr X).re := by
    rw [hs_def]; field_simp
  rw [hr_eq, hs_eq, hMr] at hRevYoung_re
  simp only [traceConjPowVar, traceConjPow, h_bridge]
  linarith

omit [Nontrivial ℋ] in
set_option backward.isDefEq.respectTransparency false in
/-- Variational attainment (−1 ≤ p < 0):
    ∃ X_opt ∈ pdSetLM achieving equality; the optimizer is X_opt = (B†A^pB)^{1/p}. -/
 lemma exists_traceConjPowVar_eq_neg {p : ℝ} (hp0 : p < 0)
    {B A : L ℋ} (hB : IsUnit B) (hA : A ∈ pdSetLM (ℋ := ℋ)) :
    ∃ X ∈ pdSetLM (ℋ := ℋ),
      p * traceConjPow (ℋ := ℋ) p B A = traceConjPowVar (ℋ := ℋ) p B A X := by
  have hA_nn := nonneg_of_pdSetLM hA
  have hpne : (p : ℝ) ≠ 0 := ne_of_lt hp0
  have hApd : CFC.rpow A p ∈ pdSetLM (ℋ := ℋ) := pdSetLM_rpow_ne hA
  set M := star B * CFC.rpow A p * B with hM_def
  have hM_nn : (0 : L ℋ) ≤ M := star_left_conjugate_nonneg CFC.rpow_nonneg _
  have hMpd : M ∈ pdSetLM (ℋ := ℋ) := pdSetLM_conj hApd hB
  have hM_unit : IsUnit M := isUnit_of_pdSetLM hMpd
  have h1p_ne : (1 : ℝ) / p ≠ 0 := by positivity
  set X_opt := CFC.rpow M (1 / p) with hX_opt_def
  have hX_opt_pd : X_opt ∈ pdSetLM (ℋ := ℋ) := pdSetLM_rpow_ne hMpd
  refine ⟨X_opt, hX_opt_pd, ?_⟩
  have hX_opt_nn := nonneg_of_pdSetLM hX_opt_pd
  have h1_sub_p_nn : 0 ≤ 1 - p := by linarith
  have h_bridge := _root_.SandwichedRenyiRelativeEntropy.liebTraceMapLM_as_lm_trace_pd B A X_opt hA hX_opt_pd h1_sub_p_nn
  have hrpow_comp : CFC.rpow X_opt (1 - p) = CFC.rpow M ((1 - p) / p) := by
    rw [hX_opt_def, CFC.rpow_eq_pow, CFC.rpow_eq_pow]
    rw [CFC.rpow_rpow M (1 / p) (1 - p) (by positivity) ⟨hM_nn, hM_unit⟩]
    congr 1; ring
  have hrpow_mul : M * CFC.rpow M ((1 - p) / p) = X_opt := by
    have h1 : CFC.rpow M 1 = M := CFC.rpow_one M hM_nn
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
set_option backward.isDefEq.respectTransparency false in
/-- Variational inequality (0 < p ≤ 1):
    ∀ X ∈ pdSetLM, F(A,X) ≤ p · traceConjPow(p,B,A).
    Follows from the trace Young inequality. -/
 lemma traceConjPowVar_le_pos {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1)
    {B A X : L ℋ} (hA : A ∈ pdSetLM (ℋ := ℋ)) (hX : X ∈ pdSetLM (ℋ := ℋ)) :
    traceConjPowVar (ℋ := ℋ) p B A X ≤ p * traceConjPow (ℋ := ℋ) p B A := by
  have hA_nn := nonneg_of_pdSetLM hA
  have hX_nn := nonneg_of_pdSetLM hX
  set M := star B * CFC.rpow A p * B with hM_def
  set N := CFC.rpow X (1 - p) with hN_def
  have hM_nn : (0 : L ℋ) ≤ M := star_left_conjugate_nonneg CFC.rpow_nonneg _
  have hN_nn : (0 : L ℋ) ≤ N := CFC.rpow_nonneg
  have hM_pos : M.IsPositive :=
    (LinearMap.nonneg_iff_isPositive _).mp hM_nn
  have hN_pos : N.IsPositive :=
    (LinearMap.nonneg_iff_isPositive _).mp hN_nn
  have h_bridge : liebTraceMapLM (ℋ := ℋ) p (star B) A X = (Tr (M * N)).re :=
    _root_.SandwichedRenyiRelativeEntropy.liebTraceMapLM_as_lm_trace hp0.le hp1 B A X hA_nn hX_nn
  have hp1' : p < 1 ∨ p = 1 := lt_or_eq_of_le hp1
  rcases hp1' with hp1' | rfl
  · have h1p : 0 < 1 - p := by linarith
    set r := 1 / p with hr_def
    set s := 1 / (1 - p) with hs_def
    have hpq : r.HolderConjugate s :=
      Real.holderConjugate_one_div hp0 h1p (by ring)
    have hYoung := trace_young_inequality hpq M N hM_pos hN_pos
    have hMr : CFC.rpow M r = CFC.rpow (star B * CFC.rpow A p * B) (1 / p) := by
      rw [hM_def]
    have hNs : CFC.rpow N s = X := by
      rw [hN_def, hs_def, CFC.rpow_eq_pow, CFC.rpow_eq_pow]
      rw [CFC.rpow_rpow_of_exponent_nonneg X (1 - p) (1 / (1 - p))
        (by linarith) (by positivity)]
      rw [show (1 - p) * (1 / (1 - p)) = 1 from by field_simp]
      exact CFC.rpow_one X hX_nn
    have hYoung_re : (Tr (M ∘ₗ N)).re ≤
        (Tr (CFC.rpow M r) / ↑r + Tr (CFC.rpow N s) / ↑s).re :=
      (RCLike.le_iff_re_im.mp hYoung).1
    rw [Complex.add_re, Complex.div_ofReal_re, Complex.div_ofReal_re, hNs] at hYoung_re
    have hMN_eq : (Tr (M ∘ₗ N)).re = (Tr (M * N)).re := by rfl
    rw [hMN_eq] at hYoung_re
    have hr_eq : (Tr (CFC.rpow M r)).re / r = p * (Tr (CFC.rpow M r)).re := by
      rw [hr_def]; field_simp
    have hs_eq : (Tr X).re / s = (1 - p) * (Tr X).re := by
      rw [hs_def]; field_simp
    rw [hr_eq, hs_eq, hMr] at hYoung_re
    simp only [traceConjPowVar, traceConjPow, h_bridge]
    linarith
  · have hN1 : N = 1 := by rw [hN_def, sub_self]; exact CFC.rpow_zero X hX_nn
    have hMN : (Tr (M * N)).re = (Tr M).re := by rw [hN1, mul_one]
    have hM1 : CFC.rpow M 1 = M := CFC.rpow_one M hM_nn
    have hFun : traceConjPow (ℋ := ℋ) 1 B A = (Tr M).re := by
      unfold traceConjPow
      rw [← hM_def, show (1 : ℝ) / 1 = 1 from by norm_num, hM1]
    have hVar : traceConjPowVar (ℋ := ℋ) 1 B A X = (Tr (M * N)).re := by
      unfold traceConjPowVar
      rw [h_bridge, sub_self, zero_mul, sub_zero]
    rw [hVar, hFun, hMN, one_mul]
end TraceConjPowConcavity
end SandwichedRenyiRelativeEntropy


