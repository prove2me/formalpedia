-- Prove2me | Definitions.Def_CRCD_Quantum_QuantumEntropy_SandwichedRenyiRelativeEntropy_part_3
-- name    : CRCD_Quantum_QuantumEntropy_SandwichedRenyiRelativeEntropy_part_3
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-08T01:07:14.225229+00:00
-- url     : https://prove2.me/theorems/f2f37cbd-9b97-43de-8216-d172871e7320
-- title:
--   Quasi-entropy invariance, tensor products, and isometric channel dilations
-- statement:
--   For positive-definite operators on a nonzero finite-dimensional complex Hilbert space, $\operatorname{Re}Q_\alpha(\rho\Vert\sigma)$ is jointly concave when $1/2\le\alpha<1$. Unitary covariance of functional calculus and cyclicity of trace give, for every real $\alpha$ and arbitrary operators,
--   $$
--   Q_\alpha(U\rho U^*\Vert U\sigma U^*)=Q_\alpha(\rho\Vert\sigma).
--   $$
--   For positive semidefinite $\rho_i,\sigma_i$ on finite-dimensional factors, and every real $\alpha$, the part proves
--   $$
--   Q_\alpha(\rho_1\otimes\rho_2\Vert\sigma_1\otimes\sigma_2)
--   =Q_\alpha(\rho_1\Vert\sigma_1)Q_\alpha(\rho_2\Vert\sigma_2).
--   $$
--   For $\tau>0$ and $\alpha\ne0$, $Q_\alpha(\tau\Vert\tau)=\operatorname{Tr}\tau$. The maximally mixed operator $I_E/\dim E$ is positive definite on every nonzero finite-dimensional environment $E$.
--
--   Every CPTP map $\Phi:L(H)\to L(K)$ with nonzero finite-dimensional input $H$ has a finite-dimensional nonzero environment $E$ and a linear isometry $V:H\to K\otimes E$ such that
--   $$
--   V^*V=I_H,\qquad \Phi(\gamma)=\operatorname{Tr}_E(V\gamma V^*)\quad(\gamma\in L(H)).
--   $$
--   A finite Kraus family with $\sum_a A_a^*A_a=I_H$ similarly gives $V\psi=\sum_a A_a\psi\otimes e_a$. The partial trace removes the second, environment factor. Further facts prove positive real trace and positive spectrum for positive-definite operators, continuity of every fixed real power on that cone, and joint continuity of $\operatorname{Re}Q_\alpha$ there for every real $\alpha$. These are trace-functional statements with no trace-one premise or bit conversion.
-- source:
--   https://github.com/Hayata-Yamasaki-Group/lean-quantum/blob/bf1c4f6aaec84948f1a1c76c0728432813404a0f/Quantum/QuantumEntropy/SandwichedRenyiRelativeEntropy.lean#L1505-L2158

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
import Definitions.Def_CRCD_Quantum_QuantumEntropy_SandwichedRenyiRelativeEntropy_part_2
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





















































end TraceConjPowConcavity

section JointConvexity

open LiebAndoTrace GeneralizedPerspectiveFunction
open scoped MatrixOrder

universe u₃

variable {ℋ : Type u₃} [Qudit ℋ] [Nontrivial ℋ]

set_option backward.isDefEq.respectTransparency false
set_option linter.style.longLine false

























set_option backward.isDefEq.respectTransparency false in
/-- Joint concavity of `(ρ, σ) ↦ Re Q_α(ρ‖σ)` on `pdSetLM × pdSetLM` for `1/2 ≤ α < 1`. -/
theorem sandwichedQuasi_re_jointlyConcave {α : ℝ} (hα_ge : 1 / 2 ≤ α) (hα_lt : α < 1) :
    JointlyConcaveOn (pdSetLM (ℋ := ℋ)) (pdSetLM (ℋ := ℋ))
      (fun ρ σ => (sandwichedQuasi (ℋ := ℋ) α ρ σ).re) := by
  intro ρ₁ ρ₂ σ₁ σ₂ θ hρ₁ hρ₂ hσ₁ hσ₂ hθ0 hθ1
  simp only [smul_eq_mul]
  set ρ_c := (1 - θ) • ρ₁ + θ • ρ₂
  set σ_c := (1 - θ) • σ₁ + θ • σ₂
  have hρ_c : ρ_c ∈ pdSetLM (ℋ := ℋ) := pdSetLM_convexCombo hρ₁ hρ₂ hθ0 hθ1
  have hσ_c : σ_c ∈ pdSetLM (ℋ := ℋ) := pdSetLM_convexCombo hσ₁ hσ₂ hθ0 hθ1
  have hα0 : (0 : ℝ) < α := by linarith
  have hα_ne1 : α ≠ 1 := ne_of_lt hα_lt
  set H_c := quasiVarOpt α ρ_c σ_c
  have hH_c_pd := quasiVarOpt_pdSetLM hα0 hα_ne1 hρ_c hσ_c
  have hH_c_pos := _root_.SandwichedRenyiRelativeEntropy.isPositive_of_pdSetLM hH_c_pd
  have hH_c_unit := isUnit_of_pdSetLM hH_c_pd
  have hH_c_eq := _root_.SandwichedRenyiRelativeEntropy.quasiVarOpt_eq_quasi_lt hα0 hα_lt hρ_c hσ_c
  have h_combo_eq : (sandwichedQuasi α ρ_c σ_c).re = (quasiVar α ρ_c σ_c H_c).re := by
    rw [← hH_c_eq]
  have h_lb1 : (sandwichedQuasi α ρ₁ σ₁).re ≤ (quasiVar α ρ₁ σ₁ H_c).re :=
    (RCLike.le_iff_re_im.mp (quasi_le_quasiVar hα0 hα_lt (_root_.SandwichedRenyiRelativeEntropy.isPositive_of_pdSetLM hρ₁)
      (_root_.SandwichedRenyiRelativeEntropy.isPositive_of_pdSetLM hσ₁) hH_c_pos (isUnit_of_pdSetLM hσ₁) hH_c_unit)).1
  have h_lb2 : (sandwichedQuasi α ρ₂ σ₂).re ≤ (quasiVar α ρ₂ σ₂ H_c).re :=
    (RCLike.le_iff_re_im.mp (quasi_le_quasiVar hα0 hα_lt (_root_.SandwichedRenyiRelativeEntropy.isPositive_of_pdSetLM hρ₂)
      (_root_.SandwichedRenyiRelativeEntropy.isPositive_of_pdSetLM hσ₂) hH_c_pos (isUnit_of_pdSetLM hσ₂) hH_c_unit)).1
  have h_sigma_concave := sigma_term_concaveOn hα0 hα_ne1 hα_ge hH_c_pd
  have h_sigma_ineq : (1 - θ) * (Tr (CFC.rpow (CFC.rpow σ₁ ((α - 1) / (2 * α)) * H_c *
          CFC.rpow σ₁ ((α - 1) / (2 * α))) (α / (α - 1)))).re +
      θ * (Tr (CFC.rpow (CFC.rpow σ₂ ((α - 1) / (2 * α)) * H_c *
          CFC.rpow σ₂ ((α - 1) / (2 * α))) (α / (α - 1)))).re ≤
      (Tr (CFC.rpow (CFC.rpow σ_c ((α - 1) / (2 * α)) * H_c *
          CFC.rpow σ_c ((α - 1) / (2 * α))) (α / (α - 1)))).re :=
    h_sigma_concave.2 hσ₁ hσ₂ (by linarith : 0 ≤ 1 - θ) hθ0 (by linarith)
  have h_trace_lin : (Tr (H_c * ρ_c)).re =
      (1 - θ) * (Tr (H_c * ρ₁)).re + θ * (Tr (H_c * ρ₂)).re := by
    change (Tr (H_c * ((1 - θ) • ρ₁ + θ • ρ₂))).re = _
    exact trace_H_mul_combo_re H_c ρ₁ ρ₂ θ
  have h_concave : (1 - θ) * (quasiVar α ρ₁ σ₁ H_c).re + θ * (quasiVar α ρ₂ σ₂ H_c).re ≤
      (quasiVar α ρ_c σ_c H_c).re := by
    unfold quasiVar
    simp only [Complex.sub_re, Complex.re_ofReal_mul]
    have hα1_neg : α - 1 < (0 : ℝ) := by linarith
    nlinarith [h_trace_lin, h_sigma_ineq]
  rw [h_combo_eq]
  calc (1 - θ) * (sandwichedQuasi α ρ₁ σ₁).re + θ * (sandwichedQuasi α ρ₂ σ₂).re
      ≤ (1 - θ) * (quasiVar α ρ₁ σ₁ H_c).re + θ * (quasiVar α ρ₂ σ₂ H_c).re := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left h_lb1 (by linarith)
        · exact mul_le_mul_of_nonneg_left h_lb2 hθ0
    _ ≤ (quasiVar α ρ_c σ_c H_c).re := h_concave

end JointConvexity

section UnitaryInvariance

universe u₄

variable {ℋ : Type u₄} [Qudit ℋ]

open scoped NNReal

instance : IsScalarTower ℝ≥0 ℂ (L ℋ) where
  smul_assoc r c x := by
    change (algebraMap ℝ≥0 ℂ r * c) • x = (algebraMap ℝ≥0 ℂ r) • (c • x)
    rw [mul_smul]

/-- Trace is invariant under unitary conjugation: Tr(U A U†) = Tr(A). -/
lemma trace_unitary_conj (A : L ℋ) (U : unitary (L ℋ)) :
    Tr ((U : L ℋ) * A * (star U : L ℋ)) = Tr A :=
  LinearMap.trace_map (Unitary.conjStarAlgAut ℂ (L ℋ) U) A

/-- CFC.rpow commutes with unitary conjugation: (U A U†)^p = U A^p U†. -/
 lemma rpow_unitary_conj (U : unitary (L ℋ)) (A : L ℋ) (p : ℝ) :
    CFC.rpow ((U : L ℋ) * A * (star U : L ℋ)) p =
      (U : L ℋ) * CFC.rpow A p * (star U : L ℋ) := by
  let φ := Unitary.conjStarAlgAut ℂ (L ℋ) U
  simp only [CFC.rpow]
  let f : ℝ≥0 → ℝ≥0 := fun x => x ^ p
  change cfc f (φ A) = φ (cfc f A)
  have hnn : (0 : L ℋ) ≤ φ A ↔ (0 : L ℋ) ≤ A := by
    conv_lhs => rw [show (0 : L ℋ) = φ 0 from (map_zero φ).symm]
    exact OrderIsoClass.map_le_map_iff φ
  have hspec : spectrum ℝ≥0 (φ A) = spectrum ℝ≥0 A :=
    AlgEquiv.spectrum_eq (φ.restrictScalars ℝ≥0).toAlgEquiv A
  by_cases h : (0 ≤ A) ∧ ContinuousOn f (spectrum ℝ≥0 A)
  · exact (StarAlgHomClass.map_cfc (S := ℂ) φ f A h.2 (map_continuous φ) h.1
      (hnn.mpr h.1)).symm
  · rw [cfc_apply_of_not_and A h, map_zero, cfc_apply_of_not_and]
    rwa [hnn, hspec]

/-- Unitary invariance of sandwichedQuasi:
    Q_α(U ρ U†‖U σ U†) = Q_α(ρ‖σ). -/
theorem sandwichedQuasi_unitary_conj (α : ℝ) (ρ σ : L ℋ) (U : unitary (L ℋ)) :
    sandwichedQuasi α ((U : L ℋ) * ρ * (star U : L ℋ))
        ((U : L ℋ) * σ * (star U : L ℋ)) =
      sandwichedQuasi α ρ σ := by
  let φ := Unitary.conjStarAlgAut ℂ (L ℋ) U
  change sandwichedQuasi α (φ ρ) (φ σ) = sandwichedQuasi α ρ σ
  unfold sandwichedQuasi
  set β := (1 - α) / (2 * α)
  set P := CFC.rpow σ β
  rw [show CFC.rpow (φ σ) β = φ (CFC.rpow σ β) from _root_.SandwichedRenyiRelativeEntropy.rpow_unitary_conj U σ β]
  have h_inner : φ P * φ ρ * φ P = φ (P * ρ * P) := by
    simp only [map_mul]
  rw [h_inner, show CFC.rpow (φ (P * ρ * P)) α = φ (CFC.rpow (P * ρ * P) α)
    from _root_.SandwichedRenyiRelativeEntropy.rpow_unitary_conj U (P * ρ * P) α]
  exact trace_unitary_conj _ U



end UnitaryInvariance

section TensorMultiplicativity

open QuantumChannel TensorProduct

variable {ℋ₁ : Type*} {ℋ₂ : Type*} [Qudit ℋ₁] [Qudit ℋ₂]

set_option backward.isDefEq.respectTransparency false in
/-- Tensor multiplicativity of sandwichedQuasi:
    Q_α(ρ₁ ⊗ ρ₂ ‖ σ₁ ⊗ σ₂) = Q_α(ρ₁ ‖ σ₁) · Q_α(ρ₂ ‖ σ₂). -/
theorem sandwichedQuasi_tensor (α : ℝ) (ρ₁ σ₁ : L ℋ₁) (ρ₂ σ₂ : L ℋ₂)
    (hρ₁ : 0 ≤ ρ₁) (hσ₁ : 0 ≤ σ₁) (hρ₂ : 0 ≤ ρ₂) (hσ₂ : 0 ≤ σ₂) :
    sandwichedQuasi α (TensorProduct.map ρ₁ ρ₂ : L (ℋ₁ ⊗[ℂ] ℋ₂))
        (TensorProduct.map σ₁ σ₂) =
      sandwichedQuasi α ρ₁ σ₁ * sandwichedQuasi α ρ₂ σ₂ := by
  unfold sandwichedQuasi
  set β := (1 - α) / (2 * α)
  set P₁ := CFC.rpow σ₁ β
  set P₂ := CFC.rpow σ₂ β
  rw [TensorCFC.rpow_tensorProduct σ₁ σ₂ β hσ₁ hσ₂,
    show TensorProduct.map P₁ P₂ * TensorProduct.map ρ₁ ρ₂ * TensorProduct.map P₁ P₂ =
      TensorProduct.map (P₁ * ρ₁ * P₁) (P₂ * ρ₂ * P₂) from by
        rw [← TensorProduct.map_mul, ← TensorProduct.map_mul],
    TensorCFC.rpow_tensorProduct (P₁ * ρ₁ * P₁) (P₂ * ρ₂ * P₂) α
      (conjugate_nonneg_of_nonneg hρ₁ CFC.rpow_nonneg)
      (conjugate_nonneg_of_nonneg hρ₂ CFC.rpow_nonneg)]
  exact LinearMap.trace_tensorProduct'
    (CFC.rpow (P₁ * ρ₁ * P₁) α) (CFC.rpow (P₂ * ρ₂ * P₂) α)



end TensorMultiplicativity

section Monotonicity

open MeasureTheory HaarUnitary QuantumChannel TensorProduct

universe u₅

variable {ℋ : Type u₅} [Qudit ℋ] [Nontrivial ℋ]

set_option linter.style.longLine false

omit [Nontrivial ℋ] in
/-- Pure-state Stinespring isometry from a Kraus family `A : κ → (ℋ →ₗ[ℂ] 𝒦)`
    (possibly different input/output spaces) satisfying `Σ_a A_a* A_a = I_ℋ`.
    The map `V ψ := Σ_a (A_a ψ) ⊗ e_a` is a linear isometry `ℋ → 𝒦 ⊗ ℂ^κ`
    realizing the channel `γ ↦ Σ_a A_a γ A_a*` as `TrRight(V γ V*)`. -/
 lemma kraus_to_pure_stinespring_isometry
    {𝒦 : Type u₅} [Qudit 𝒦]
    {κ : Type u₅} [Fintype κ] [DecidableEq κ]
    (A : κ → (ℋ →ₗ[ℂ] 𝒦))
    (hSumAA : (∑ a : κ, (LinearMap.adjoint (A a)).comp (A a)) = (1 : L ℋ)) :
    ∃ V : ℋ →ₗ[ℂ] 𝒦 ⊗[ℂ] EuclideanSpace ℂ κ,
      (LinearMap.adjoint V).comp V = (1 : L ℋ) ∧
      ∀ γ : L ℋ,
        (∑ a : κ, (A a).comp (γ.comp (LinearMap.adjoint (A a)))) =
          TrRight ((V.comp γ).comp (LinearMap.adjoint V)) := by
  classical
  -- The Stinespring isometry from QuantumChannel.lean.
  refine ⟨krausToStinespringOperator (ℋ₁ := ℋ) (ℋ₂ := 𝒦) A, ?_, ?_⟩
  · -- `V* V = Σ_a A_a* A_a = 1` by `hSumAA`.
    set V := krausToStinespringOperator (ℋ₁ := ℋ) (ℋ₂ := 𝒦) A with hV_def
    apply LinearMap.ext
    intro ψ
    -- Reduce to computing `(V* V) ψ` directly.
    have hVψ : V ψ = ∑ a : κ, (A a ψ) ⊗ₜ[ℂ] (EuclideanSpace.basisFun κ ℂ a) :=
      krausToStinespringOperator_apply (ℋ₁ := ℋ) (ℋ₂ := 𝒦) A ψ
    have hcomp : (V.adjoint.comp V) ψ = V.adjoint (V ψ) := rfl
    rw [hcomp, hVψ, map_sum]
    have hpiece : ∀ a : κ,
        V.adjoint ((A a ψ) ⊗ₜ[ℂ] (EuclideanSpace.basisFun κ ℂ a)) =
          (LinearMap.adjoint (A a)) (A a ψ) := by
      intro a
      simpa [hV_def] using
        adjoint_krausToStinespringOperator_tmul_basisFun
          (ℋ₁ := ℋ) (ℋ₂ := 𝒦) A (A a ψ) a
    -- Replace each summand and recognize `Σ_a A_a* A_a = 1`.
    simp_rw [hpiece]
    have hSumApp :
        (∑ a : κ, (LinearMap.adjoint (A a)).comp (A a)) ψ = (1 : L ℋ) ψ := by
      rw [hSumAA]
    -- LHS sum equals `(∑ a, A_a* ∘ A_a) ψ`.
    have hsum_eq :
        (∑ a : κ, (LinearMap.adjoint (A a)) (A a ψ)) =
          (∑ a : κ, (LinearMap.adjoint (A a)).comp (A a)) ψ := by
      simp [LinearMap.sum_apply]
    rw [hsum_eq, hSumApp]
  · -- Partial-trace identity: this is exactly `trRight_kraus`.
    intro γ
    have h := trRight_kraus (ℋ₁ := ℋ) (ℋ₂ := 𝒦) A γ
    exact h.symm

/-- **Stinespring dilation theorem (Form A, isometric / pure-environment form).**

    Every quantum channel `E : CPTP ℋ 𝒦` (possibly different input/output
    spaces) admits an *isometric* Stinespring dilation: there exists a
    finite-dimensional environment Hilbert space
    `ℋ_env`, a linear map `V : ℋ →ₗ[ℂ] (𝒦 ⊗ ℋ_env)` satisfying
      `V*V = I_ℋ` (isometry),
    and
      `E(γ) = TrRight(V γ V*)` for every `γ : L ℋ`,
    where `TrRight` traces out the *second* (environment) factor.

    This is the form directly available from
    `QuantumChannel.cp_to_stinespring` strengthened by trace preservation,
    and matches **Watrous Cor. 2.27** in its pure-environment incarnation
    (also Frank–Lieb arXiv:1306.5358 with `τ` chosen pure).

    The previous unitary form
      `E(γ) = Tr₂(U (τ ⊗ γ) U*)`
    with positive-definite `τ` on the environment (Form B / Naimark) is
    strictly stronger and is **not** used downstream after the present
    refactor; the data-processing inequality is proved directly from this
    Form A statement following the Frank–Lieb scheme. -/
theorem CPTP.exists_stinespring_dilation {𝒦 : Type u₅} [Qudit 𝒦] (E : CPTP ℋ 𝒦) :
    ∃ (ℋ_env : Type u₅) (_ : Qudit ℋ_env) (_ : Nontrivial ℋ_env)
      (V : ℋ →ₗ[ℂ] (𝒦 ⊗[ℂ] ℋ_env)),
        (LinearMap.adjoint V).comp V = (1 : L ℋ) ∧
        ∀ γ : L ℋ,
          E.toFun γ = TrRight ((V.comp γ).comp (LinearMap.adjoint V)) := by
  classical
  -- Extract a Kraus representation of E.
  have hE_cp : IsCompletelyPositive E.toLinearMap :=
    ⟨E.toCompletelyPositiveMap, rfl⟩
  let bℋ := Module.Free.chooseBasis ℂ ℋ
  have hKraus : HasKraus (E.toLinearMap) :=
    cp_to_kraus bℋ E.toLinearMap hE_cp
  obtain ⟨κ, hκ_dec, hκ_fin, A, hA_eq⟩ := hKraus
  letI : DecidableEq κ := hκ_dec
  letI : Fintype κ := hκ_fin
  -- Trace preservation gives Σ_a A_a* A_a = 1 (same derivation as before).
  set S : L ℋ := ∑ a : κ, (LinearMap.adjoint (A a)).comp (A a) with hS_def
  have hSρ_tr : ∀ ρ : L ℋ, Tr (S * ρ) = Tr ρ := by
    intro ρ
    have htr : Tr ρ = Tr (E.toLinearMap ρ) := E.trace_map ρ
    have hKr : E.toLinearMap ρ =
        ∑ a : κ, (A a).comp (ρ.comp (LinearMap.adjoint (A a))) := hA_eq ρ
    have hcycle : ∀ a : κ,
        Tr ((A a).comp (ρ.comp (LinearMap.adjoint (A a)))) =
          Tr (((LinearMap.adjoint (A a)).comp (A a)) * ρ) := by
      intro a
      -- Cyclicity across the mixed spaces `ℋ → 𝒦`:
      -- `Tr_𝒦 (Aₐ ∘ ρ ∘ Aₐ*) = Tr_ℋ ((ρ ∘ Aₐ*) ∘ Aₐ) = Tr_ℋ (ρ ∘ (Aₐ* ∘ Aₐ))`.
      rw [← LinearMap.trace_comp_comm' (A a) (ρ.comp (LinearMap.adjoint (A a))),
          LinearMap.comp_assoc, Module.End.mul_eq_comp]
      -- Now `Tr (ρ ∘ (Aₐ* ∘ Aₐ)) = Tr ((Aₐ* ∘ Aₐ) ∘ ρ)`, a cyclic swap within `L ℋ`.
      exact (LinearMap.trace_comp_comm' ρ ((LinearMap.adjoint (A a)).comp (A a))).symm
    calc Tr (S * ρ)
        = Tr ((∑ a : κ, (LinearMap.adjoint (A a)).comp (A a)) * ρ) := by rw [hS_def]
      _ = ∑ a : κ, Tr (((LinearMap.adjoint (A a)).comp (A a)) * ρ) := by
          rw [Finset.sum_mul]; exact map_sum Tr _ _
      _ = ∑ a : κ, Tr ((A a).comp (ρ.comp (LinearMap.adjoint (A a)))) := by
          refine Finset.sum_congr rfl ?_
          intro a _; rw [(hcycle a).symm]
      _ = Tr (∑ a : κ, (A a).comp (ρ.comp (LinearMap.adjoint (A a)))) := by
          rw [map_sum Tr]
      _ = Tr (E.toLinearMap ρ) := by rw [← hKr]
      _ = Tr ρ := htr.symm
  have hSumAA : S = (1 : L ℋ) := by
    apply LinearMap.ext
    intro v
    refine ext_inner_left ℂ ?_
    intro w
    have h_compOuter : ∀ M : L ℋ, M.comp (outer_product w v) = outer_product w (M v) := by
      intro M
      ext x
      simp [outer_product_eq_rankOne]
    have htrace_eq : Tr (S * (outer_product w v)) = Tr (outer_product w v) :=
      hSρ_tr (outer_product w v)
    have hLHS : Tr (S * (outer_product w v)) = inner ℂ w (S v) := by
      change Tr (S.comp (outer_product w v)) = inner ℂ w (S v)
      rw [h_compOuter S, trace_outer_product]
    have hRHS : Tr (outer_product w v) = inner ℂ w v := trace_outer_product w v
    have h1v : (1 : L ℋ) v = v := rfl
    rw [h1v]
    rw [← hLHS, htrace_eq, hRHS]
  -- The environment is `EuclideanSpace ℂ κ`. We need it `Nontrivial`, which is
  -- equivalent to `κ` being nonempty. The hypothesis `Σ A_a* A_a = 1 ≠ 0`
  -- (since `ℋ` is nontrivial, so `1 ≠ 0`) forces `κ` to be nonempty.
  have hκ_nonempty : Nonempty κ := by
    by_contra h
    rw [not_nonempty_iff] at h
    have hS_zero : S = 0 := by
      simp [hS_def, Finset.sum_empty]
    have h1ne : (1 : L ℋ) ≠ 0 := one_ne_zero
    apply h1ne
    rw [← hSumAA, hS_zero]
  haveI : Nonempty κ := hκ_nonempty
  haveI : Nontrivial (EuclideanSpace ℂ κ) :=
    Module.nontrivial_of_finrank_pos
      (by
        rw [finrank_euclideanSpace]
        exact Fintype.card_pos)
  -- Pure-state Stinespring isometry from the Kraus family.
  obtain ⟨V, hV_iso, hV_eq⟩ :=
    _root_.SandwichedRenyiRelativeEntropy.kraus_to_pure_stinespring_isometry (ℋ := ℋ) A hSumAA
  refine ⟨EuclideanSpace ℂ κ, inferInstance, inferInstance, V, hV_iso, ?_⟩
  intro γ
  have hKraus_γ : E.toFun γ =
      ∑ a : κ, (A a).comp (γ.comp (LinearMap.adjoint (A a))) := hA_eq γ
  rw [hKraus_γ, hV_eq γ]

omit [Nontrivial ℋ] in
/-- For any positive-definite operator `τ` and any nonzero exponent `α`,
    `sandwichedQuasi α τ τ = Tr τ`. In particular, for a density operator
    (`Tr τ = 1`) this gives `Q_α(τ‖τ) = 1`. -/
lemma sandwichedQuasi_self_pdSetLM
    {α : ℝ} (hα_ne : α ≠ 0) {τ : L ℋ} (hτ : τ ∈ pdSetLM (ℋ := ℋ)) :
    sandwichedQuasi α τ τ = Tr τ := by
  unfold sandwichedQuasi
  have hτ_nn := nonneg_of_pdSetLM hτ
  have hτ_unit := isUnit_of_pdSetLM hτ
  have h2α_ne : (2 * α : ℝ) ≠ 0 := mul_ne_zero (by norm_num) hα_ne
  set β : ℝ := (1 - α) / (2 * α) with hβ_def
  have hexp1 : β + 1 + β = 1 / α := by rw [hβ_def]; field_simp; ring
  -- τ^β · τ · τ^β = τ^(1/α)
  have h_middle : CFC.rpow τ β * τ * CFC.rpow τ β = CFC.rpow τ (1 / α) := by
    have h_τ1 : τ = CFC.rpow τ 1 := (CFC.rpow_one τ hτ_nn).symm
    calc CFC.rpow τ β * τ * CFC.rpow τ β
        = CFC.rpow τ β * CFC.rpow τ 1 * CFC.rpow τ β := by rw [← h_τ1]
      _ = CFC.rpow τ (β + 1) * CFC.rpow τ β := by
          simp only [CFC.rpow_eq_pow]
          rw [← CFC.rpow_add hτ_unit]
      _ = CFC.rpow τ (β + 1 + β) := by
          simp only [CFC.rpow_eq_pow]
          rw [← CFC.rpow_add hτ_unit]
      _ = CFC.rpow τ (1 / α) := by rw [hexp1]
  rw [h_middle]
  -- (τ^(1/α))^α = τ
  have h_outer : CFC.rpow (CFC.rpow τ (1 / α)) α = τ := by
    have h1α_ne : (1 / α : ℝ) ≠ 0 := one_div_ne_zero hα_ne
    simp only [CFC.rpow_eq_pow]
    rw [CFC.rpow_rpow τ (1 / α) α h1α_ne ⟨hτ_nn, hτ_unit⟩]
    rw [show (1 / α) * α = 1 from by field_simp]
    exact CFC.rpow_one τ hτ_nn
  rw [h_outer]

/-- The maximally mixed state on a finite-dimensional Hilbert space is positive definite. -/
lemma maxmixed_pdSetLM (ℋ_env : Type u₅) [Qudit ℋ_env] [Nontrivial ℋ_env] :
    ((Module.finrank ℂ ℋ_env : ℂ)⁻¹ • (1 : L ℋ_env)) ∈ pdSetLM (ℋ := ℋ_env) := by
  set d : ℕ := Module.finrank ℂ ℋ_env
  have hd_pos : 0 < d := Module.finrank_pos
  have hd_ne : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd_pos.ne'
  set c : ℂ := (d : ℂ)⁻¹
  have hc_ne : c ≠ 0 := inv_ne_zero hd_ne
  -- `0 ≤ c` in `ℂ` (using `ComplexOrder`): `c.re ≥ 0` and `c.im = 0`.
  have hc_nn : (0 : ℂ) ≤ c := by
    refine ⟨?_, ?_⟩
    · change 0 ≤ ((d : ℂ)⁻¹).re
      rw [Complex.inv_re]
      have hd_re : ((d : ℂ)).re = (d : ℝ) := Complex.natCast_re d
      have hd_im : ((d : ℂ)).im = 0 := Complex.natCast_im d
      rw [hd_re,
          show Complex.normSq (d : ℂ) = (d : ℝ)^2 from by
            rw [Complex.normSq_apply, hd_re, hd_im]; ring]
      positivity
    · symm
      change ((d : ℂ)⁻¹).im = 0
      rw [Complex.inv_im]
      simp [Complex.natCast_im]
  -- `(c • 1).IsPositive` via `LinearMap.isPositive_one.smul_of_nonneg`.
  have h_isPos : ((c • (1 : L ℋ_env)) : L ℋ_env).IsPositive :=
    LinearMap.isPositive_one.smul_of_nonneg hc_nn
  have h_nn : (0 : L ℋ_env) ≤ c • (1 : L ℋ_env) :=
    (LinearMap.nonneg_iff_isPositive _).mpr h_isPos
  -- `c • 1` is a unit (inverse is `c⁻¹ • 1`).
  have h_unit : IsUnit (c • (1 : L ℋ_env)) := by
    refine ⟨⟨c • 1, c⁻¹ • 1, ?_, ?_⟩, rfl⟩
    · rw [smul_mul_smul_comm, mul_inv_cancel₀ hc_ne, mul_one, one_smul]
    · rw [smul_mul_smul_comm, inv_mul_cancel₀ hc_ne, mul_one, one_smul]
  -- Push positivity and unit-ness through the CLM iso.
  have h_clm_nn : (0 : LownerHeinzTheorem.L ℋ_env) ≤
      (c • (1 : L ℋ_env)).toContinuousLinearMap :=
    map_nonneg (toCLMStarAlgHom (ℋ := ℋ_env)) h_nn
  have h_clm_unit : IsUnit (c • (1 : L ℋ_env)).toContinuousLinearMap :=
    (toCLMStarAlgHom (ℋ := ℋ_env)).toRingHom.isUnit_map h_unit
  have h_clm_sa : IsSelfAdjoint (c • (1 : L ℋ_env)).toContinuousLinearMap :=
    IsSelfAdjoint.of_nonneg h_clm_nn
  refine ⟨h_clm_sa, ?_⟩
  intro r hr
  have h_spec_nn : spectrum ℝ (c • (1 : L ℋ_env)).toContinuousLinearMap ⊆ Set.Ici 0 :=
    (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) _ (ha := h_clm_sa)).1 h_clm_nn
  rcases lt_or_eq_of_le (by simpa [Set.Ici] using h_spec_nn hr) with h | h
  · exact h
  · exfalso; rw [← h] at hr
    exact (spectrum.zero_notMem_iff (R := ℝ)).mpr h_clm_unit hr



/-- For any positive-definite operator in `pdSetLM`, the trace is a real positive number.
    Proof: trace = sum of eigenvalues; each eigenvalue is ≥ 0 (from positivity) and ≠ 0
    (from invertibility), hence > 0. The sum over a nonempty index set of positives is positive. -/
lemma trace_re_pos_of_pdSetLM {A : L ℋ} (hA : A ∈ pdSetLM (ℋ := ℋ)) :
    0 < (Tr A).re := by
  have hA_nn := nonneg_of_pdSetLM hA
  have hA_pos : A.IsPositive := (LinearMap.nonneg_iff_isPositive _).mp hA_nn
  have hA_sym := hA_pos.isSymmetric
  have hA_unit := isUnit_of_pdSetLM hA
  set n := Module.finrank ℂ ℋ with hn_def
  have hn : Module.finrank ℂ ℋ = n := rfl
  have hn_pos : 0 < n := Module.finrank_pos
  -- Re (Tr A) = ∑ eigenvalues.
  rw [show (Tr A).re = ∑ i, hA_sym.eigenvalues hn i from
        hA_sym.re_trace_eq_sum_eigenvalues hn]
  -- Each eigenvalue is positive; the sum over a nonempty index set is positive.
  have h_nonempty : (Finset.univ : Finset (Fin n)).Nonempty :=
    ⟨⟨0, hn_pos⟩, Finset.mem_univ _⟩
  apply Finset.sum_pos _ h_nonempty
  intro i _
  -- eigenvalues are ≥ 0 from `IsPositive.nonneg_eigenvalues`.
  have hlam_nn : 0 ≤ hA_sym.eigenvalues hn i := hA_pos.nonneg_eigenvalues hn i
  -- eigenvalues are ≠ 0 because `A` is a unit (so `0 ∉ spectrum`).
  rcases lt_or_eq_of_le hlam_nn with hpos | hzero
  · exact hpos
  · exfalso
    have h_eig : Module.End.HasEigenvalue A ((hA_sym.eigenvalues hn i : ℂ)) :=
      hA_sym.hasEigenvalue_eigenvalues hn i
    rw [← hzero] at h_eig
    push_cast at h_eig
    obtain ⟨v, hv_mem, hv_ne⟩ := h_eig.exists_hasEigenvector
    have hAv : A v = 0 := by
      rw [Module.End.mem_eigenspace_iff] at hv_mem
      simpa using hv_mem
    obtain ⟨uA, huA⟩ := hA_unit
    have h_inv_mul : (↑uA⁻¹ : L ℋ) * A = 1 := by rw [← huA, Units.inv_mul]
    have hv_eq : v = ((↑uA⁻¹ : L ℋ) * A) v := by rw [h_inv_mul]; rfl
    rw [show ((↑uA⁻¹ : L ℋ) * A) v = (↑uA⁻¹ : L ℋ) (A v) from rfl, hAv, map_zero] at hv_eq
    exact hv_ne hv_eq



/-- The `ℝ≥0`-spectrum of any operator in `pdSetLM` lies in `Set.Ioi 0`. -/
 lemma pdSetLM_spectrum_nnreal_subset_Ioi
    {ℋ_aux : Type u₅} [Qudit ℋ_aux] [Nontrivial ℋ_aux]
    {A : L ℋ_aux} (hA : A ∈ pdSetLM (ℋ := ℋ_aux)) :
    spectrum ℝ≥0 A ⊆ Set.Ioi 0 := by
  intro r hr
  have hA_unit : IsUnit A := isUnit_of_pdSetLM hA
  have h0_notMem : (0 : ℝ≥0) ∉ spectrum ℝ≥0 A :=
    (spectrum.zero_notMem_iff (R := ℝ≥0)).mpr hA_unit
  rcases lt_or_eq_of_le (show (0 : ℝ≥0) ≤ r from zero_le) with hr_pos | hr_zero
  · exact hr_pos
  · exact absurd (hr_zero ▸ hr) h0_notMem

/-- For each fixed real exponent `p`, the map `A ↦ CFC.rpow A p` is continuous on `pdSetLM`. -/
 lemma rpow_continuousOn_pdSetLM
    {ℋ_aux : Type u₅} [Qudit ℋ_aux] [Nontrivial ℋ_aux] (p : ℝ) :
    ContinuousOn (fun A : L ℋ_aux => CFC.rpow A p) (pdSetLM (ℋ := ℋ_aux)) := by
  -- `CFC.rpow A p = cfc (· ^ p : ℝ≥0 → ℝ≥0) A`. Apply `ContinuousOn.cfc_nnreal_of_mem_nhdsSet`.
  have h_subset : (⋃ A ∈ pdSetLM (ℋ := ℋ_aux), spectrum ℝ≥0 A) ⊆ Set.Ioi 0 := by
    intro r hr
    rw [Set.mem_iUnion₂] at hr
    obtain ⟨A, hA, hrA⟩ := hr
    exact _root_.SandwichedRenyiRelativeEntropy.pdSetLM_spectrum_nnreal_subset_Ioi hA hrA
  have h_nhds : (Set.Ioi 0 : Set ℝ≥0) ∈ 𝓝ˢ (⋃ A ∈ pdSetLM (ℋ := ℋ_aux), spectrum ℝ≥0 A) :=
    isOpen_Ioi.mem_nhdsSet.mpr h_subset
  have h_id_cont : ContinuousOn (fun A : L ℋ_aux => A) (pdSetLM (ℋ := ℋ_aux)) := continuousOn_id
  have h_nn : ∀ A ∈ pdSetLM (ℋ := ℋ_aux), (0 : L ℋ_aux) ≤ A :=
    fun _ hA => nonneg_of_pdSetLM hA
  have h_f_cont : ContinuousOn (fun x : ℝ≥0 => x ^ p) (Set.Ioi 0) :=
    NNReal.continuousOn_rpow_const (.inl (by simp : (0 : ℝ≥0) ∉ Set.Ioi 0))
  exact h_id_cont.cfc_nnreal_of_mem_nhdsSet (s := Set.Ioi 0) (f := (· ^ p))
    h_nhds (ha' := h_nn) (hf := h_f_cont)

/-- Continuity of `(ρ, σ) ↦ σ^β * ρ * σ^β` on `pdSetLM × pdSetLM`. -/
 lemma rpow_conj_continuousOn_pdSetLM
    {ℋ_aux : Type u₅} [Qudit ℋ_aux] [Nontrivial ℋ_aux] (β : ℝ) :
    ContinuousOn
      (fun p : L ℋ_aux × L ℋ_aux => CFC.rpow p.2 β * p.1 * CFC.rpow p.2 β)
      (pdSetLM (ℋ := ℋ_aux) ×ˢ pdSetLM (ℋ := ℋ_aux)) := by
  have h_rpow_snd : ContinuousOn (fun p : L ℋ_aux × L ℋ_aux => CFC.rpow p.2 β)
      (pdSetLM (ℋ := ℋ_aux) ×ˢ pdSetLM (ℋ := ℋ_aux)) :=
    (_root_.SandwichedRenyiRelativeEntropy.rpow_continuousOn_pdSetLM (ℋ_aux := ℋ_aux) β).comp continuousOn_snd
      (fun _ hx => (Set.mem_prod.mp hx).2)
  have h_fst : ContinuousOn (fun p : L ℋ_aux × L ℋ_aux => p.1)
      (pdSetLM (ℋ := ℋ_aux) ×ˢ pdSetLM (ℋ := ℋ_aux)) := continuousOn_fst
  exact (h_rpow_snd.mul h_fst).mul h_rpow_snd

/-- The conjugated operator `σ^β * ρ * σ^β` belongs to `pdSetLM` for `ρ, σ ∈ pdSetLM`. -/
 lemma rpow_conj_mem_pdSetLM
    {ℋ_aux : Type u₅} [Qudit ℋ_aux] [Nontrivial ℋ_aux] (β : ℝ) {ρ σ : L ℋ_aux}
    (hρ : ρ ∈ pdSetLM (ℋ := ℋ_aux)) (hσ : σ ∈ pdSetLM (ℋ := ℋ_aux)) :
    (CFC.rpow σ β * ρ * CFC.rpow σ β) ∈ pdSetLM (ℋ := ℋ_aux) := by
  have hP_pd : CFC.rpow σ β ∈ pdSetLM (ℋ := ℋ_aux) := pdSetLM_rpow_ne hσ
  have hP_sa : IsSelfAdjoint (CFC.rpow σ β) :=
    IsSelfAdjoint.of_nonneg (nonneg_of_pdSetLM hP_pd)
  have hP_unit : IsUnit (CFC.rpow σ β) := isUnit_of_pdSetLM hP_pd
  have h_eq : CFC.rpow σ β * ρ * CFC.rpow σ β =
      star (CFC.rpow σ β) * ρ * CFC.rpow σ β := by rw [hP_sa.star_eq]
  rw [h_eq]; exact pdSetLM_conj hρ hP_unit

/-- The real part of `sandwichedQuasi` is jointly continuous on `pdSetLM × pdSetLM`.
    Built from continuity of `CFC.rpow` (via `ContinuousOn.cfc_nnreal_of_mem_nhdsSet`),
    continuity of multiplication, and continuity of `Tr`. -/
lemma sandwichedQuasi_re_continuousOn_pdSetLM
    {ℋ_aux : Type u₅} [Qudit ℋ_aux] [Nontrivial ℋ_aux] (α : ℝ) :
    ContinuousOn (Function.uncurry (fun (ρ σ : L ℋ_aux) => (sandwichedQuasi α ρ σ).re))
      (pdSetLM (ℋ := ℋ_aux) ×ˢ pdSetLM (ℋ := ℋ_aux)) := by
  set β : ℝ := (1 - α) / (2 * α)
  -- Step 1: `(ρ, σ) ↦ σ^β * ρ * σ^β` is continuous, and its image lies in `pdSetLM`.
  have h_inner_cont :
      ContinuousOn (fun p : L ℋ_aux × L ℋ_aux => CFC.rpow p.2 β * p.1 * CFC.rpow p.2 β)
        (pdSetLM (ℋ := ℋ_aux) ×ˢ pdSetLM (ℋ := ℋ_aux)) :=
    _root_.SandwichedRenyiRelativeEntropy.rpow_conj_continuousOn_pdSetLM β
  have h_inner_mem : ∀ p ∈ pdSetLM (ℋ := ℋ_aux) ×ˢ pdSetLM (ℋ := ℋ_aux),
      CFC.rpow p.2 β * p.1 * CFC.rpow p.2 β ∈ pdSetLM (ℋ := ℋ_aux) := by
    rintro ⟨ρ, σ⟩ ⟨hρ, hσ⟩
    exact _root_.SandwichedRenyiRelativeEntropy.rpow_conj_mem_pdSetLM β hρ hσ
  -- Step 2: `A ↦ A^α` is continuous on operators whose spectrum lies in `Set.Ioi 0`.
  have h_nhds :
      (Set.Ioi 0 : Set ℝ≥0) ∈
        𝓝ˢ (⋃ p ∈ pdSetLM (ℋ := ℋ_aux) ×ˢ pdSetLM (ℋ := ℋ_aux),
          spectrum ℝ≥0 (CFC.rpow p.2 β * p.1 * CFC.rpow p.2 β)) := by
    apply isOpen_Ioi.mem_nhdsSet.mpr
    intro r hr
    rw [Set.mem_iUnion₂] at hr
    obtain ⟨p, hp, hpr⟩ := hr
    exact _root_.SandwichedRenyiRelativeEntropy.pdSetLM_spectrum_nnreal_subset_Ioi (h_inner_mem p hp) hpr
  have h_nn : ∀ p ∈ pdSetLM (ℋ := ℋ_aux) ×ˢ pdSetLM (ℋ := ℋ_aux),
      (0 : L ℋ_aux) ≤ CFC.rpow p.2 β * p.1 * CFC.rpow p.2 β :=
    fun p hp => nonneg_of_pdSetLM (h_inner_mem p hp)
  have h_f_cont : ContinuousOn (fun x : ℝ≥0 => x ^ α) (Set.Ioi 0) :=
    NNReal.continuousOn_rpow_const (.inl (by simp : (0 : ℝ≥0) ∉ Set.Ioi 0))
  have h_pow_cont :
      ContinuousOn
        (fun p : L ℋ_aux × L ℋ_aux =>
          CFC.rpow (CFC.rpow p.2 β * p.1 * CFC.rpow p.2 β) α)
        (pdSetLM (ℋ := ℋ_aux) ×ˢ pdSetLM (ℋ := ℋ_aux)) :=
    h_inner_cont.cfc_nnreal_of_mem_nhdsSet (s := Set.Ioi (0 : ℝ≥0)) (f := (· ^ α))
      h_nhds (ha' := h_nn) (hf := h_f_cont)
  -- Step 3: `Tr` and `Re` are continuous.
  have h_trace_cont : Continuous (fun A : L ℋ_aux => Tr A) :=
    LinearMap.continuous_of_finiteDimensional _
  have h_final :
      ContinuousOn
        (fun p : L ℋ_aux × L ℋ_aux =>
          (Tr (CFC.rpow (CFC.rpow p.2 β * p.1 * CFC.rpow p.2 β) α)).re)
        (pdSetLM (ℋ := ℋ_aux) ×ˢ pdSetLM (ℋ := ℋ_aux)) :=
    Complex.continuous_re.comp_continuousOn (h_trace_cont.comp_continuousOn h_pow_cont)
  exact h_final
end Monotonicity
end SandwichedRenyiRelativeEntropy


