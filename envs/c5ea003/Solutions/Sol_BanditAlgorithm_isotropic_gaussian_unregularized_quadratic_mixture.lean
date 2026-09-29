-- Prove2me | solution 1 for BanditAlgorithm.isotropic_gaussian_unregularized_quadratic_mixture
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-29T15:22:46.006001+00:00
-- url     : https://prove2.me/submissions/a0849092-8763-4cac-beb3-70ef42a0e27d

import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Matrix.Order
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Distributions.Gaussian.Real

open MeasureTheory ProbabilityTheory Matrix
open scoped MatrixOrder ENNReal

namespace BanditAlgorithm

private lemma dot_mulVec_comm_of_isHermitian
    {d : ℕ} {K : Matrix (Fin d) (Fin d) ℝ}
    (hK : K.IsHermitian) (x y : Fin d → ℝ) :
    x ⬝ᵥ K *ᵥ y = y ⬝ᵥ K *ᵥ x := by
  simp only [dotProduct, Matrix.mulVec]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have hsym : K j i = K i j := by
    have heq := congrArg (fun M : Matrix (Fin d) (Fin d) ℝ => M i j) hK.eq
    simpa using heq
  rw [hsym]
  ring

private lemma quadratic_completion
    {d : ℕ} {K : Matrix (Fin d) (Fin d) ℝ}
    (hK : K.PosDef) (S x : Fin d → ℝ) :
    x ⬝ᵥ S - 1 / 2 * (x ⬝ᵥ K *ᵥ x) =
      1 / 2 * (S ⬝ᵥ K⁻¹ *ᵥ S) -
        1 / 2 * ((x - K⁻¹ *ᵥ S) ⬝ᵥ K *ᵥ (x - K⁻¹ *ᵥ S)) := by
  have hunit : IsUnit K := hK.isUnit
  have hdetunit : IsUnit K.det :=
    (Matrix.isUnit_iff_isUnit_det K).mp hunit
  have hKS : K *ᵥ (K⁻¹ *ᵥ S) = S := by
    rw [mulVec_mulVec, mul_nonsing_inv K hdetunit]
    exact one_mulVec S
  have hcomm (u v : Fin d → ℝ) :
      u ⬝ᵥ K *ᵥ v = v ⬝ᵥ K *ᵥ u :=
    dot_mulVec_comm_of_isHermitian hK.isHermitian u v
  simp only [Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct]
  rw [hKS, hcomm (K⁻¹ *ᵥ S) x, hKS,
    dotProduct_comm (K⁻¹ *ᵥ S) S]
  ring

private lemma sqrt_mulVec_sq
    {d : ℕ} {K : Matrix (Fin d) (Fin d) ℝ}
    (hK : K.PosDef) (x : Fin d → ℝ) :
    x ⬝ᵥ K *ᵥ x =
      (CFC.sqrt K *ᵥ x) ⬝ᵥ (CFC.sqrt K *ᵥ x) := by
  let B := CFC.sqrt K
  have hBps : B.PosSemidef :=
    nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg K)
  have hBB : B * B = K :=
    CFC.sqrt_mul_sqrt_self K hK.posSemidef.nonneg
  have hxvec : x ᵥ* B = B *ᵥ x := by
    have heq := vecMul_conjTranspose B x
    rw [hBps.isHermitian.eq] at heq
    simpa [B] using heq
  calc
    x ⬝ᵥ K *ᵥ x = x ⬝ᵥ (B * B) *ᵥ x := by rw [hBB]
    _ = x ⬝ᵥ B *ᵥ (B *ᵥ x) := by rw [mulVec_mulVec]
    _ = (B *ᵥ x) ⬝ᵥ (B *ᵥ x) := by rw [dotProduct_mulVec, hxvec]

private lemma isotropic_b_integrable {d : ℕ} {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : Fin d → ℝ => Real.exp (-b * (x ⬝ᵥ x))) := by
  have hcoord : ∀ i : Fin d,
      Integrable (fun r : ℝ => Real.exp (-b * r ^ 2)) :=
    fun _ => integrable_exp_neg_mul_sq hb
  have hprod := Integrable.fintype_prod hcoord
  have heq : (fun x : Fin d → ℝ => Real.exp (-b * (x ⬝ᵥ x))) =
      fun x => ∏ i : Fin d, Real.exp (-b * (x i) ^ 2) := by
    funext x
    simp only [dotProduct, ← Real.exp_sum]
    congr 2
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [heq, volume_pi]
  exact hprod

private lemma isotropic_b_integral (d : ℕ) (b : ℝ) :
    (∫ x : Fin d → ℝ, Real.exp (-b * (x ⬝ᵥ x))) =
      (Real.sqrt (Real.pi / b)) ^ d := by
  have heq : (fun x : Fin d → ℝ => Real.exp (-b * (x ⬝ᵥ x))) =
      fun x => ∏ i : Fin d, Real.exp (-b * (x i) ^ 2) := by
    funext x
    simp only [dotProduct, ← Real.exp_sum]
    congr 2
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [heq, integral_fintype_prod_volume_eq_prod
    (f := fun (_ : Fin d) (r : ℝ) => Real.exp (-b * r ^ 2))]
  rw [show (∫ r : ℝ, Real.exp (-b * r ^ 2)) =
      Real.sqrt (Real.pi / b) by exact integral_gaussian b,
    Finset.prod_const]
  simp

private lemma isotropic_integrable (d : ℕ) :
    Integrable (fun x : Fin d → ℝ => Real.exp (-1 / 2 * (x ⬝ᵥ x))) := by
  have hcoord : ∀ i : Fin d,
      Integrable (fun r : ℝ => Real.exp (-1 / 2 * r ^ 2)) :=
    fun _ => by
      simpa only [neg_div] using
        integrable_exp_neg_mul_sq (show 0 < (1 / 2 : ℝ) by norm_num)
  have hprod := Integrable.fintype_prod hcoord
  have heq : (fun x : Fin d → ℝ => Real.exp (-1 / 2 * (x ⬝ᵥ x))) =
      fun x => ∏ i : Fin d, Real.exp (-1 / 2 * (x i) ^ 2) := by
    funext x
    simp only [dotProduct, ← Real.exp_sum]
    congr 2
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [heq, volume_pi]
  exact hprod

private lemma isotropic_integral (d : ℕ) :
    (∫ x : Fin d → ℝ, Real.exp (-1 / 2 * (x ⬝ᵥ x))) =
      (Real.sqrt (Real.pi / (1 / 2 : ℝ))) ^ d := by
  have heq : (fun x : Fin d → ℝ => Real.exp (-1 / 2 * (x ⬝ᵥ x))) =
      fun x => ∏ i : Fin d, Real.exp (-1 / 2 * (x i) ^ 2) := by
    funext x
    simp only [dotProduct, ← Real.exp_sum]
    congr 2
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [heq, integral_fintype_prod_volume_eq_prod
    (f := fun (_ : Fin d) (r : ℝ) => Real.exp (-1 / 2 * r ^ 2))]
  have hscalar :
      (∫ r : ℝ, Real.exp (-1 / 2 * r ^ 2)) =
        Real.sqrt (Real.pi / (1 / 2 : ℝ)) := by
    simpa only [neg_div] using integral_gaussian (1 / 2 : ℝ)
  rw [hscalar, Finset.prod_const]
  simp

private lemma centered_quadratic_integrable
    {d : ℕ} {K : Matrix (Fin d) (Fin d) ℝ} (hK : K.PosDef) :
    Integrable (fun x : Fin d → ℝ =>
      Real.exp (-1 / 2 * (x ⬝ᵥ K *ᵥ x))) := by
  let B := CFC.sqrt K
  have hBdet : B.det ≠ 0 := by
    rw [hK.posSemidef.det_sqrt]
    simpa using (Real.sqrt_pos.2 hK.det_pos).ne'
  have hBmeas : Measurable (toLin' B) :=
    (LinearMap.continuous_on_pi (toLin' B)).measurable
  have hmap :
      Measure.map (toLin' B) volume =
        ENNReal.ofReal (abs B.det⁻¹) • volume :=
    Real.map_matrix_volume_pi_eq_smul_volume_pi hBdet
  have hgsmul :
      Integrable (fun y : Fin d → ℝ => Real.exp (-1 / 2 * (y ⬝ᵥ y)))
        (Measure.map (toLin' B) volume) := by
    rw [hmap]
    exact (isotropic_integrable d).smul_measure (by finiteness)
  have hcomp := hgsmul.comp_measurable hBmeas
  simpa only [Function.comp_apply, toLin'_apply,
    sqrt_mulVec_sq hK] using hcomp

private lemma centered_quadratic_integral
    {d : ℕ} {K : Matrix (Fin d) (Fin d) ℝ} (hK : K.PosDef) :
    (∫ x : Fin d → ℝ, Real.exp (-1 / 2 * (x ⬝ᵥ K *ᵥ x))) =
      (ENNReal.ofReal (abs (CFC.sqrt K).det⁻¹)).toReal *
      (Real.sqrt (Real.pi / (1 / 2 : ℝ))) ^ d := by
  let B := CFC.sqrt K
  have hBdet : B.det ≠ 0 := by
    rw [hK.posSemidef.det_sqrt]
    simpa using (Real.sqrt_pos.2 hK.det_pos).ne'
  have hBmeas : Measurable (toLin' B) :=
    (LinearMap.continuous_on_pi (toLin' B)).measurable
  have hgsm :
      AEStronglyMeasurable
        (fun y : Fin d → ℝ => Real.exp (-1 / 2 * (y ⬝ᵥ y)))
        (Measure.map (toLin' B) volume) := by
    have hm : Measurable
        (fun y : Fin d → ℝ => Real.exp (-1 / 2 * (y ⬝ᵥ y))) := by
      simp only [dotProduct]
      fun_prop
    exact hm.aestronglyMeasurable
  have hi := integral_map hBmeas.aemeasurable hgsm
  rw [Real.map_matrix_volume_pi_eq_smul_volume_pi hBdet,
    integral_smul_measure] at hi
  rw [isotropic_integral d] at hi
  simpa only [B, toLin'_apply, sqrt_mulVec_sq hK] using hi.symm

private lemma shifted_quadratic_integrable
    {d : ℕ} {K : Matrix (Fin d) (Fin d) ℝ}
    (hK : K.PosDef) (S : Fin d → ℝ) :
    Integrable (fun x : Fin d → ℝ =>
      Real.exp (x ⬝ᵥ S - 1 / 2 * (x ⬝ᵥ K *ᵥ x))) := by
  let c := K⁻¹ *ᵥ S
  have heq :
      (fun x : Fin d → ℝ =>
        Real.exp (x ⬝ᵥ S - 1 / 2 * (x ⬝ᵥ K *ᵥ x))) =
      fun x =>
        Real.exp (1 / 2 * (S ⬝ᵥ K⁻¹ *ᵥ S)) *
          Real.exp (-1 / 2 * ((x - c) ⬝ᵥ K *ᵥ (x - c))) := by
    funext x
    rw [← Real.exp_add]
    congr 1
    convert quadratic_completion hK S x using 1 <;> simp only [c] <;> ring
  rw [heq]
  exact ((centered_quadratic_integrable hK).comp_sub_right c).const_mul _

private lemma shifted_quadratic_integral
    {d : ℕ} {K : Matrix (Fin d) (Fin d) ℝ}
    (hK : K.PosDef) (S : Fin d → ℝ) :
    (∫ x : Fin d → ℝ,
      Real.exp (x ⬝ᵥ S - 1 / 2 * (x ⬝ᵥ K *ᵥ x))) =
      Real.exp (1 / 2 * (S ⬝ᵥ K⁻¹ *ᵥ S)) *
        (ENNReal.ofReal (abs (CFC.sqrt K).det⁻¹)).toReal *
          (Real.sqrt (Real.pi / (1 / 2 : ℝ))) ^ d := by
  let c := K⁻¹ *ᵥ S
  have heq :
      (fun x : Fin d → ℝ =>
        Real.exp (x ⬝ᵥ S - 1 / 2 * (x ⬝ᵥ K *ᵥ x))) =
      fun x =>
        Real.exp (1 / 2 * (S ⬝ᵥ K⁻¹ *ᵥ S)) *
          Real.exp (-1 / 2 * ((x - c) ⬝ᵥ K *ᵥ (x - c))) := by
    funext x
    rw [← Real.exp_add]
    congr 1
    convert quadratic_completion hK S x using 1 <;> simp only [c] <;> ring
  have htrans :
      (∫ a : Fin d → ℝ,
        Real.exp (-1 / 2 * ((a - c) ⬝ᵥ K *ᵥ (a - c)))) =
      ∫ a : Fin d → ℝ, Real.exp (-1 / 2 * (a ⬝ᵥ K *ᵥ a)) :=
    integral_sub_right_eq_self
      (fun a : Fin d → ℝ => Real.exp (-1 / 2 * (a ⬝ᵥ K *ᵥ a))) c
  rw [heq, integral_const_mul, htrans, centered_quadratic_integral hK]
  ring

private lemma gaussian_normalization
    {d : ℕ} {lam : ℝ} (hlam : 0 < lam)
    {K : Matrix (Fin d) (Fin d) ℝ} (hK : K.PosDef) :
    ((Real.sqrt (Real.pi / (lam / 2))) ^ d)⁻¹ *
          |(CFC.sqrt K).det|⁻¹ *
        (Real.sqrt Real.pi * Real.sqrt 2) ^ d =
      Real.exp (-1 / 2 * Real.log (K.det / lam ^ d)) := by
  let L : ℝ :=
    ((Real.sqrt (Real.pi / (lam / 2))) ^ d)⁻¹ *
          |(CFC.sqrt K).det|⁻¹ *
        (Real.sqrt Real.pi * Real.sqrt 2) ^ d
  let R : ℝ := Real.exp (-1 / 2 * Real.log (K.det / lam ^ d))
  have hdet : 0 < K.det := hK.det_pos
  have hdetB :
      (CFC.sqrt K).det = Real.sqrt K.det := by
    simpa using hK.posSemidef.det_sqrt
  have hBpos : 0 < (CFC.sqrt K).det := by
    rw [hdetB]
    exact Real.sqrt_pos.2 hdet
  have hL : 0 ≤ L := by
    dsimp [L]
    positivity
  have hR : 0 ≤ R := by
    dsimp [R]
    positivity
  apply (sq_eq_sq₀ hL hR).mp
  have hJ2 :
      ((Real.sqrt (Real.pi / (lam / 2))) ^ d) ^ 2 =
        (Real.pi / (lam / 2)) ^ d := by
    calc
      _ = (Real.sqrt (Real.pi / (lam / 2)) ^ 2) ^ d := by
        simp only [← pow_mul]
        congr 1
        omega
      _ = _ := by
        rw [Real.sq_sqrt]
        positivity
  have hB2 : |(CFC.sqrt K).det| ^ 2 = K.det := by
    rw [abs_of_pos hBpos, hdetB, Real.sq_sqrt hdet.le]
  have hC2 :
      ((Real.sqrt Real.pi * Real.sqrt 2) ^ d) ^ 2 =
        (Real.pi * 2) ^ d := by
    calc
      _ = ((Real.sqrt Real.pi * Real.sqrt 2) ^ 2) ^ d := by
        simp only [← pow_mul]
        congr 1
        omega
      _ = _ := by
        congr 1
        rw [mul_pow, Real.sq_sqrt Real.pi_pos.le,
          Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hratio : 0 < K.det / lam ^ d := div_pos hdet (pow_pos hlam d)
  change L ^ 2 = R ^ 2
  have hR2 : R ^ 2 = (K.det / lam ^ d)⁻¹ := by
    dsimp [R]
    rw [← Real.exp_nat_mul]
    have hexpArg :
        (↑(2 : ℕ) : ℝ) * (-1 / 2 * Real.log (K.det / lam ^ d)) =
          -Real.log (K.det / lam ^ d) := by
      ring
    rw [hexpArg]
    rw [Real.exp_neg, Real.exp_log hratio]
  rw [hR2]
  dsimp [L]
  rw [mul_pow, mul_pow, inv_pow, inv_pow, hJ2, hB2, hC2]
  field_simp [hlam.ne', hdet.ne', Real.pi_ne_zero]
  rw [← mul_pow]
  congr 1
  field_simp [hlam.ne']

end BanditAlgorithm

theorem solution
    {d : ℕ} {lam : ℝ} (hlam : 0 < lam) :
    ∃ h : Measure (Fin d → ℝ),
      IsProbabilityMeasure h ∧
      ∀ (S : Fin d → ℝ) (V : Matrix (Fin d) (Fin d) ℝ),
        V.PosSemidef →
        Integrable
            (fun x => Real.exp
              (x ⬝ᵥ S - 1 / 2 * (x ⬝ᵥ V *ᵥ x))) h ∧
          (∫ x, Real.exp
              (x ⬝ᵥ S - 1 / 2 * (x ⬝ᵥ V *ᵥ x)) ∂h) =
            Real.exp
              (1 / 2 *
                (S ⬝ᵥ (lam • (1 : Matrix (Fin d) (Fin d) ℝ) + V)⁻¹ *ᵥ S -
                  Real.log
                    ((lam • (1 : Matrix (Fin d) (Fin d) ℝ) + V).det / lam ^ d))) := by
  let b : ℝ := lam / 2
  let J : ℝ := (Real.sqrt (Real.pi / b)) ^ d
  let q : (Fin d → ℝ) → ℝ :=
    fun x => J⁻¹ * Real.exp (-b * (x ⬝ᵥ x))
  let ρ : (Fin d → ℝ) → ℝ≥0∞ := fun x => ENNReal.ofReal (q x)
  let h : Measure (Fin d → ℝ) := volume.withDensity ρ
  have hb : 0 < b := by dsimp [b]; positivity
  have hJ : 0 < J := by
    dsimp [J]
    positivity
  have hqnonneg : ∀ x, 0 ≤ q x := by
    intro x
    exact mul_nonneg (inv_nonneg.mpr hJ.le) (Real.exp_pos _).le
  have hqmeas : Measurable q := by
    dsimp [q]
    simp only [dotProduct]
    fun_prop
  have hρmeas : Measurable ρ :=
    hqmeas.ennreal_ofReal
  have hρtop : ∀ᵐ x ∂(volume : Measure (Fin d → ℝ)), ρ x < ∞ :=
    Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top
  have hqint : Integrable q := by
    dsimp [q]
    exact (BanditAlgorithm.isotropic_b_integrable hb).const_mul _
  have hqone : (∫ x, q x) = 1 := by
    dsimp [q]
    rw [integral_const_mul, BanditAlgorithm.isotropic_b_integral d b]
    dsimp [J]
    exact inv_mul_cancel₀ hJ.ne'
  have hhprob : IsProbabilityMeasure h := by
    change IsProbabilityMeasure (volume.withDensity ρ)
    constructor
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    rw [← ofReal_integral_eq_lintegral_ofReal hqint
      (Filter.Eventually.of_forall hqnonneg)]
    rw [hqone]
    simp
  refine ⟨h, hhprob, ?_⟩
  intro S V hV
  let K : Matrix (Fin d) (Fin d) ℝ :=
    lam • (1 : Matrix (Fin d) (Fin d) ℝ) + V
  have hlamI : (lam • (1 : Matrix (Fin d) (Fin d) ℝ)).PosDef :=
    Matrix.PosDef.one.smul hlam
  have hK : K.PosDef := hlamI.add_posSemidef hV
  have hquad (x : Fin d → ℝ) :
      x ⬝ᵥ K *ᵥ x = lam * (x ⬝ᵥ x) + x ⬝ᵥ V *ᵥ x := by
    simp only [K, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_add, dotProduct_smul]
    ring
  have hcombine (x : Fin d → ℝ) :
      (ρ x).toReal *
          Real.exp (x ⬝ᵥ S - 1 / 2 * (x ⬝ᵥ V *ᵥ x)) =
        J⁻¹ * Real.exp (x ⬝ᵥ S - 1 / 2 * (x ⬝ᵥ K *ᵥ x)) := by
    rw [show ρ x = ENNReal.ofReal (q x) by rfl,
      ENNReal.toReal_ofReal (hqnonneg x)]
    dsimp [q]
    rw [mul_assoc, ← Real.exp_add]
    congr 1
    rw [hquad]
    dsimp [b]
    ring
  constructor
  · change Integrable
      (fun x => Real.exp (x ⬝ᵥ S - 1 / 2 * (x ⬝ᵥ V *ᵥ x)))
      (volume.withDensity ρ)
    rw [integrable_withDensity_iff_integrable_smul' hρmeas hρtop]
    have hi :=
      (BanditAlgorithm.shifted_quadratic_integrable hK S).const_mul J⁻¹
    apply hi.congr
    exact Filter.Eventually.of_forall fun x => by
      simpa only [smul_eq_mul] using (hcombine x).symm
  · change (∫ x, Real.exp
        (x ⬝ᵥ S - 1 / 2 * (x ⬝ᵥ V *ᵥ x)) ∂volume.withDensity ρ) = _
    rw [integral_withDensity_eq_integral_toReal_smul hρmeas hρtop]
    have hint :
        (∫ x, (ρ x).toReal •
            Real.exp (x ⬝ᵥ S - 1 / 2 * (x ⬝ᵥ V *ᵥ x))) =
          J⁻¹ * ∫ x,
            Real.exp (x ⬝ᵥ S - 1 / 2 * (x ⬝ᵥ K *ᵥ x)) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        simpa only [smul_eq_mul] using hcombine x
    rw [hint, BanditAlgorithm.shifted_quadratic_integral hK S]
    have hnorm := BanditAlgorithm.gaussian_normalization hlam hK
    have hJdef :
        J = (Real.sqrt (Real.pi / (lam / 2))) ^ d := by
      rfl
    calc
      J⁻¹ *
          (Real.exp (1 / 2 * (S ⬝ᵥ K⁻¹ *ᵥ S)) *
              (ENNReal.ofReal |(CFC.sqrt K).det⁻¹|).toReal *
            (Real.sqrt (Real.pi / (1 / 2 : ℝ))) ^ d) =
          Real.exp (1 / 2 * (S ⬝ᵥ K⁻¹ *ᵥ S)) *
            (((Real.sqrt (Real.pi / (lam / 2))) ^ d)⁻¹ *
              |(CFC.sqrt K).det|⁻¹ *
                (Real.sqrt Real.pi * Real.sqrt 2) ^ d) := by
            rw [hJdef]
            have hBpos : 0 < (CFC.sqrt K).det := by
              rw [hK.posSemidef.det_sqrt]
              simpa using Real.sqrt_pos.2 hK.det_pos
            rw [ENNReal.toReal_ofReal (abs_nonneg _),
              abs_inv, abs_of_pos hBpos]
            have hsqrt :
                Real.sqrt (Real.pi / (1 / 2 : ℝ)) =
                  Real.sqrt Real.pi * Real.sqrt 2 := by
              rw [show Real.pi / (1 / 2 : ℝ) = Real.pi * 2 by ring,
                Real.sqrt_mul Real.pi_pos.le]
            rw [hsqrt]
            ring
      _ = Real.exp (1 / 2 * (S ⬝ᵥ K⁻¹ *ᵥ S)) *
            Real.exp (-1 / 2 * Real.log (K.det / lam ^ d)) := by
          rw [hnorm]
      _ = Real.exp
            (1 / 2 *
              (S ⬝ᵥ K⁻¹ *ᵥ S - Real.log (K.det / lam ^ d))) := by
          rw [← Real.exp_add]
          congr 1
          ring
      _ = Real.exp
            (1 / 2 *
              (S ⬝ᵥ
                  (lam • (1 : Matrix (Fin d) (Fin d) ℝ) + V)⁻¹ *ᵥ S -
                Real.log
                  ((lam • (1 : Matrix (Fin d) (Fin d) ℝ) + V).det /
                    lam ^ d))) := by
          rfl
