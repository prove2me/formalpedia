-- Prove2me | solution 1 for BanditAlgorithm.least_squares_confidence_ellipsoid
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:22:04.895585+00:00
-- url     : https://prove2.me/submissions/ff7dd678-01d3-46c3-8d2a-145669e0848c

import Definitions.Def_SelfNormalizedProcess
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Data.Real.StarOrdered
import Mathlib.Tactic
import Theorems.Thm_BanditAlgorithm_self_normalized_martingale_bound
import Mathlib.MeasureTheory.Measure.Real

open Matrix BanditAlgorithm

namespace RidgeConfidence

/- Verbatim helper by Harry_Xu, accepted submission
825d42cb-1a71-4e2a-8b2e-70fffe405640, in a local namespace.
Original source SHA-256:
ae5c6857e18343b4a437fbaf6442e45237c23cc2dd54739792fd577faed9d3c1. -/
private lemma inverse_weighted_cauchy {d : ℕ}
    {V : Matrix (Fin d) (Fin d) ℝ} (hV : V.PosDef)
    (a w : Fin d → ℝ) :
    (a ⬝ᵥ w) ^ 2 ≤
      (a ⬝ᵥ V⁻¹ *ᵥ a) * (w ⬝ᵥ V *ᵥ w) := by
  let B := Matrix.toBilin' V⁻¹
  have hBnonneg : ∀ z, 0 ≤ B z z := by
    intro z
    simpa [B, Matrix.toBilin'_apply'] using
      hV.inv.posSemidef.dotProduct_mulVec_nonneg z
  have hBsymm : LinearMap.IsSymm B := by
    constructor
    intro z y
    simp only [B, Matrix.toBilin'_apply', RingHom.id_apply,
      dotProduct, Matrix.mulVec]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    have hsymm : V⁻¹ i j = V⁻¹ j i := by
      simpa using hV.inv.isHermitian.apply j i
    rw [hsymm]
    ring
  have hcs := B.apply_sq_le_of_symm hBnonneg hBsymm a (V *ᵥ w)
  have hcancel : V⁻¹ *ᵥ (V *ᵥ w) = w := by
    rw [Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul V (hV.isUnit.map Matrix.detMonoidHom),
      Matrix.one_mulVec]
  simpa [B, Matrix.toBilin'_apply', hcancel, dotProduct_comm] using hcs

theorem regularized_posDef {Ω : Type*} {d : ℕ} {lam : ℝ}
    (hlam : 0 < lam) (A : ℕ → Ω → Fin d → ℝ) (t : ℕ) (ω : Ω) :
    (regularizedDesignMatrix d lam A t ω).PosDef := by
  unfold regularizedDesignMatrix
  exact (Matrix.PosDef.one.smul hlam).add_posSemidef
    (Matrix.posSemidef_sum (Finset.range t)
      fun _ _ ↦ by simpa using Matrix.posSemidef_vecMulVec_self_star _)

theorem regularized_coercive {Ω : Type*} {d : ℕ} (lam : ℝ)
    (A : ℕ → Ω → Fin d → ℝ) (t : ℕ) (ω : Ω) (e : Fin d → ℝ) :
    lam * (e ⬝ᵥ e) ≤ e ⬝ᵥ regularizedDesignMatrix d lam A t ω *ᵥ e := by
  have hG : (∑ s ∈ Finset.range t,
      vecMulVec (A (s + 1) ω) (A (s + 1) ω)).PosSemidef :=
    Matrix.posSemidef_sum (Finset.range t)
      fun _ _ ↦ by simpa using Matrix.posSemidef_vecMulVec_self_star _
  have hnonneg := hG.dotProduct_mulVec_nonneg e
  simp only [star_trivial] at hnonneg
  simp only [regularizedDesignMatrix, Matrix.add_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul]
  linarith

theorem ridge_normal_equation {Ω : Type*} {d : ℕ}
    (A : ℕ → Ω → Fin d → ℝ) (η X : ℕ → Ω → ℝ) (θs : Fin d → ℝ)
    (hX : ∀ (t : ℕ) (ω : Ω), X (t + 1) ω = θs ⬝ᵥ A (t + 1) ω + η (t + 1) ω)
    {lam : ℝ} (hlam : 0 < lam) (t : ℕ) (ω : Ω) :
    regularizedDesignMatrix d lam A t ω *ᵥ
        (regularizedLeastSquares d lam A X t ω - θs) =
      selfNormalizedSum d η A t ω - lam • θs := by
  have hV := regularized_posDef hlam A t ω
  have hinverse : regularizedDesignMatrix d lam A t ω *ᵥ
      regularizedLeastSquares d lam A X t ω =
        ∑ s ∈ Finset.range t, X (s + 1) ω • A (s + 1) ω := by
    rw [regularizedLeastSquares, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ (hV.isUnit.map Matrix.detMonoidHom), Matrix.one_mulVec]
  have hmodel : (∑ s ∈ Finset.range t, X (s + 1) ω • A (s + 1) ω) =
      (∑ s ∈ Finset.range t, vecMulVec (A (s + 1) ω) (A (s + 1) ω)) *ᵥ θs +
        selfNormalizedSum d η A t ω := by
    rw [Matrix.sum_mulVec, selfNormalizedSum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s hs
    rw [hX, add_smul, Matrix.vecMulVec_mulVec]
    ext i
    simp [dotProduct_comm, mul_comm]
  rw [Matrix.mulVec_sub, hinverse, hmodel, regularizedDesignMatrix,
    Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  abel

theorem ridge_error_le {Ω : Type*} {d : ℕ}
    (A : ℕ → Ω → Fin d → ℝ) (η X : ℕ → Ω → ℝ) (θs : Fin d → ℝ)
    (hX : ∀ (t : ℕ) (ω : Ω), X (t + 1) ω = θs ⬝ᵥ A (t + 1) ω + η (t + 1) ω)
    {lam : ℝ} (hlam : 0 < lam) (t : ℕ) (ω : Ω) :
    Real.sqrt ((regularizedLeastSquares d lam A X t ω - θs) ⬝ᵥ
        regularizedDesignMatrix d lam A t ω *ᵥ
          (regularizedLeastSquares d lam A X t ω - θs)) ≤
      Real.sqrt lam * Real.sqrt (θs ⬝ᵥ θs) +
        Real.sqrt (selfNormalizedSum d η A t ω ⬝ᵥ
          (regularizedDesignMatrix d lam A t ω)⁻¹ *ᵥ selfNormalizedSum d η A t ω) := by
  let V := regularizedDesignMatrix d lam A t ω
  let e := regularizedLeastSquares d lam A X t ω - θs
  let s := selfNormalizedSum d η A t ω
  let E := e ⬝ᵥ V *ᵥ e
  let Q := s ⬝ᵥ V⁻¹ *ᵥ s
  have hV : V.PosDef := regularized_posDef hlam A t ω
  have hE : 0 ≤ E := hV.posSemidef.dotProduct_mulVec_nonneg e
  have hQ : 0 ≤ Q := hV.inv.posSemidef.dotProduct_mulVec_nonneg s
  have hθ : 0 ≤ θs ⬝ᵥ θs := by
    exact Finset.sum_nonneg (fun i _ ↦ mul_self_nonneg (θs i))
  have hcoercive : lam * (e ⬝ᵥ e) ≤ E := regularized_coercive lam A t ω e
  have hnormal : V *ᵥ e = s - lam • θs := ridge_normal_equation A η X θs hX hlam t ω
  have henergy : E = e ⬝ᵥ s - lam * (e ⬝ᵥ θs) := by
    change e ⬝ᵥ V *ᵥ e = _
    rw [hnormal, dotProduct_sub, dotProduct_smul, smul_eq_mul]
  have hnoise : e ⬝ᵥ s ≤ Real.sqrt Q * Real.sqrt E := by
    have h := Real.le_sqrt_of_sq_le (inverse_weighted_cauchy hV s e)
    simpa only [dotProduct_comm s e, Real.sqrt_mul hQ, Q, E] using h
  have hcs : (e ⬝ᵥ θs) ^ 2 ≤ (θs ⬝ᵥ θs) * (e ⬝ᵥ e) := by
    simpa only [inv_one, Matrix.one_mulVec, dotProduct_comm θs e] using
      inverse_weighted_cauchy (Matrix.PosDef.one (n := Fin d) (R := ℝ)) θs e
  have hbiasSq : (-lam * (e ⬝ᵥ θs)) ^ 2 ≤ (lam * (θs ⬝ᵥ θs)) * E := by
    have h₁ := mul_le_mul_of_nonneg_left hcs (sq_nonneg lam)
    have h₂ := mul_le_mul_of_nonneg_left hcoercive (mul_nonneg hlam.le hθ)
    nlinarith
  have hbias : -lam * (e ⬝ᵥ θs) ≤
      (Real.sqrt lam * Real.sqrt (θs ⬝ᵥ θs)) * Real.sqrt E := by
    have h := Real.le_sqrt_of_sq_le hbiasSq
    simpa only [Real.sqrt_mul (mul_nonneg hlam.le hθ), Real.sqrt_mul hlam.le] using h
  change Real.sqrt E ≤ Real.sqrt lam * Real.sqrt (θs ⬝ᵥ θs) + Real.sqrt Q
  by_cases hzero : E = 0
  · rw [hzero, Real.sqrt_zero]
    positivity
  have hEpos : 0 < E := lt_of_le_of_ne hE (Ne.symm hzero)
  have hcombined : Real.sqrt E * Real.sqrt E ≤
      Real.sqrt E * (Real.sqrt lam * Real.sqrt (θs ⬝ᵥ θs) + Real.sqrt Q) := by
    nlinarith [Real.sq_sqrt hE]
  exact (mul_le_mul_iff_right₀ (Real.sqrt_pos.mpr hEpos)).mp hcombined

end RidgeConfidence

open MeasureTheory ProbabilityTheory Matrix BanditAlgorithm

theorem solution
    {Ω : Type} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {d : ℕ} (ℱ : Filtration ℕ mΩ)
    (A : ℕ → Ω → Fin d → ℝ) (η : ℕ → Ω → ℝ) (X : ℕ → Ω → ℝ) (θs : Fin d → ℝ)
    (hA : ∀ t : ℕ, Measurable[ℱ t] (A (t + 1)))
    (hη : ∀ t : ℕ, Measurable[ℱ (t + 1)] (η (t + 1)))
    (hsg : ∀ t : ℕ, HasCondSubgaussianMGF (ℱ t) (ℱ.le t) (η (t + 1)) 1 P)
    (hX : ∀ (t : ℕ) (ω : Ω), X (t + 1) ω = θs ⬝ᵥ A (t + 1) ω + η (t + 1) ω)
    {lam : ℝ} (hlam : 0 < lam) {δ : ℝ} (hδ : δ ∈ Set.Ioo (0 : ℝ) 1) :
    1 - δ ≤ P.real {ω | ∀ t : ℕ,
        Real.sqrt ((regularizedLeastSquares d lam A X t ω - θs) ⬝ᵥ
            regularizedDesignMatrix d lam A t ω *ᵥ
              (regularizedLeastSquares d lam A X t ω - θs))
          < Real.sqrt lam * Real.sqrt (θs ⬝ᵥ θs)
            + Real.sqrt (2 * Real.log (1 / δ)
                + Real.log ((regularizedDesignMatrix d lam A t ω).det / lam ^ d))} := by
  let bad : Set Ω := {ω | ∃ t : ℕ,
      2 * Real.log (1 / δ)
          + Real.log ((regularizedDesignMatrix d lam A t ω).det / lam ^ d)
        ≤ selfNormalizedSum d η A t ω ⬝ᵥ
            (regularizedDesignMatrix d lam A t ω)⁻¹ *ᵥ
              selfNormalizedSum d η A t ω}
  have hbad : P.real bad ≤ δ :=
    BanditAlgorithm.self_normalized_martingale_bound ℱ A η hA hη hsg hlam hδ
  have hcover : 1 ≤ P.real bad + P.real badᶜ := by
    simpa only [Set.union_compl_self, probReal_univ] using
      (measureReal_union_le (μ := P) bad badᶜ)
  have hprob : 1 - δ ≤ P.real badᶜ := by linarith
  refine hprob.trans (measureReal_mono ?_)
  intro ω hω t
  have hstrict : selfNormalizedSum d η A t ω ⬝ᵥ
      (regularizedDesignMatrix d lam A t ω)⁻¹ *ᵥ
        selfNormalizedSum d η A t ω <
      2 * Real.log (1 / δ)
        + Real.log ((regularizedDesignMatrix d lam A t ω).det / lam ^ d) := by
    exact lt_of_not_ge (fun ht => hω ⟨t, ht⟩)
  have hnonneg : 0 ≤ selfNormalizedSum d η A t ω ⬝ᵥ
      (regularizedDesignMatrix d lam A t ω)⁻¹ *ᵥ
        selfNormalizedSum d η A t ω :=
    (RidgeConfidence.regularized_posDef hlam A t ω).inv.posSemidef.dotProduct_mulVec_nonneg _
  have hsqrt := Real.sqrt_lt_sqrt hnonneg hstrict
  have herror := RidgeConfidence.ridge_error_le A η X θs hX hlam t ω
  linarith
