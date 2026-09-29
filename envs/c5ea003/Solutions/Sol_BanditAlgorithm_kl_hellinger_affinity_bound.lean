-- Prove2me | solution 1 for BanditAlgorithm.kl_hellinger_affinity_bound
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-04T23:55:02.279851+00:00
-- url     : https://prove2.me/submissions/38937345-3fa3-42b2-83af-a3cd3430eeae

import Mathlib

open MeasureTheory InformationTheory
open scoped ENNReal

theorem solution {Ω : Type} {mΩ : MeasurableSpace Ω}
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hD : klDiv P Q ≠ ∞) :
    ENNReal.ofReal (Real.exp (-(klDiv P Q).toReal)) ≤
      (∫⁻ ω, (P.rnDeriv (P + Q) ω * Q.rnDeriv (P + Q) ω) ^ (2⁻¹ : ℝ)
        ∂(P + Q)) ^ 2 := by
  obtain ⟨hPQ, hint⟩ := (klDiv_ne_top_iff).mp hD
  set ν : Measure Ω := P + Q with hν
  set r : Ω → ℝ≥0∞ := P.rnDeriv Q with hr
  have hrm : Measurable r := Measure.measurable_rnDeriv P Q
  have hQν : Q ≪ ν := Measure.absolutelyContinuous_of_le (Measure.le_add_left le_rfl)
  have hKL : (klDiv P Q).toReal = ∫ x, llr P Q x ∂P :=
    toReal_klDiv_of_measure_eq hPQ (by simp)
  -- Step B: the affinity integral equals `∫⁻ √r dQ`.
  have hB : ∫⁻ ω, (P.rnDeriv ν ω * Q.rnDeriv ν ω) ^ (2⁻¹ : ℝ) ∂ν =
      ∫⁻ ω, r ω ^ (2⁻¹ : ℝ) ∂Q := by
    have hmul : P.rnDeriv Q * Q.rnDeriv ν =ᵐ[ν] P.rnDeriv ν := Measure.rnDeriv_mul_rnDeriv hPQ
    have h1 : ∫⁻ ω, (P.rnDeriv ν ω * Q.rnDeriv ν ω) ^ (2⁻¹ : ℝ) ∂ν =
        ∫⁻ ω, Q.rnDeriv ν ω * r ω ^ (2⁻¹ : ℝ) ∂ν := by
      refine lintegral_congr_ae ?_
      filter_upwards [hmul] with ω hω
      have hω' : P.rnDeriv ν ω = r ω * Q.rnDeriv ν ω := by
        rw [← hω]; rfl
      rw [hω', mul_assoc, ← sq, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
        ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
      norm_num
      ring
    rw [h1]
    exact lintegral_rnDeriv_mul hQν ((hrm.pow_const _).aemeasurable)
  -- Step C: `∫⁻ √r dQ = ∫⁻ r^{-1/2} dP`.
  have hC : ∫⁻ ω, r ω ^ (2⁻¹ : ℝ) ∂Q = ∫⁻ ω, r ω ^ (-(2⁻¹ : ℝ)) ∂P := by
    rw [← lintegral_rnDeriv_mul hPQ ((hrm.pow_const _).aemeasurable)]
    refine lintegral_congr_ae ?_
    filter_upwards [Measure.rnDeriv_lt_top P Q] with ω hω
    by_cases h0 : r ω = 0
    · have h0' : P.rnDeriv Q ω = 0 := h0
      simp [h0, h0', ENNReal.zero_rpow_of_pos (by norm_num : (0:ℝ) < 2⁻¹)]
    · have hsplit : r ω ^ (2⁻¹ : ℝ) = r ω ^ (1 : ℝ) * r ω ^ (-(2⁻¹ : ℝ)) := by
        rw [← ENNReal.rpow_add _ _ h0 hω.ne]; norm_num
      rw [hsplit, ENNReal.rpow_one]
  -- Step D: the function `exp(-½ llr) = r^{-1/2}` and its integrability under `P`.
  set f : Ω → ℝ := fun x => -(2⁻¹ : ℝ) * llr P Q x with hf
  have hfint : Integrable f P := hint.const_mul _
  have hpos : ∀ᵐ x ∂P, 0 < r x := Measure.rnDeriv_pos hPQ
  have hfin : ∀ᵐ x ∂P, r x < ∞ := hPQ.ae_le (Measure.rnDeriv_lt_top P Q)
  have hexp : ∀ᵐ x ∂P, ENNReal.ofReal (Real.exp (f x)) = r x ^ (-(2⁻¹ : ℝ)) := by
    filter_upwards [hpos, hfin] with x hx0 hxt
    have hpos' : 0 < (r x).toReal := ENNReal.toReal_pos hx0.ne' hxt.ne
    have hfx : f x = Real.log (r x).toReal * (-(2⁻¹ : ℝ)) := by
      rw [hf]; dsimp only; rw [llr_def]; ring
    rw [hfx, ← Real.rpow_def_of_pos hpos', ← ENNReal.ofReal_rpow_of_pos hpos',
      ENNReal.ofReal_toReal hxt.ne]
  have hllr_meas : Measurable (llr P Q) := Real.measurable_log.comp hrm.ennreal_toReal
  have hmeas : Measurable (fun x => Real.exp (f x)) :=
    Real.measurable_exp.comp (measurable_const.mul hllr_meas)
  have hsqrt_le : ∀ x : ℝ≥0∞, x ^ (2⁻¹ : ℝ) ≤ 1 + x := by
    intro x
    rcases le_or_gt x 1 with hx | hx
    · calc x ^ (2⁻¹ : ℝ) ≤ (1 : ℝ≥0∞) ^ (2⁻¹ : ℝ) := ENNReal.rpow_le_rpow hx (by norm_num)
        _ = 1 := ENNReal.one_rpow _
        _ ≤ 1 + x := le_self_add
    · calc x ^ (2⁻¹ : ℝ) ≤ x ^ (1 : ℝ) :=
            ENNReal.rpow_le_rpow_of_exponent_le hx.le (by norm_num)
        _ = x := ENNReal.rpow_one _
        _ ≤ 1 + x := le_add_self
  have hfin_int : ∫⁻ x, ENNReal.ofReal (Real.exp (f x)) ∂P < ∞ := by
    rw [lintegral_congr_ae hexp, ← hC]
    calc ∫⁻ ω, r ω ^ (2⁻¹ : ℝ) ∂Q ≤ ∫⁻ ω, (1 + r ω) ∂Q := lintegral_mono fun ω => hsqrt_le _
      _ < ∞ := by
          rw [lintegral_add_left measurable_const, lintegral_const, Measure.lintegral_rnDeriv hPQ]
          simp
  have hgint : Integrable (fun x => Real.exp (f x)) P :=
    ⟨hmeas.aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x => (Real.exp_pos _).le)).mpr hfin_int⟩
  -- Step E: Jensen for the exponential.
  have hJ : Real.exp (∫ x, f x ∂P) ≤ ∫ x, Real.exp (f x) ∂P :=
    convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
      (ae_of_all _ fun _ => Set.mem_univ _) hfint hgint
  have hfint_eq : ∫ x, f x ∂P = -(2⁻¹ : ℝ) * (klDiv P Q).toReal := by
    rw [hf, integral_const_mul, hKL]
  have hsq : Real.exp (-(klDiv P Q).toReal) = (Real.exp (∫ x, f x ∂P)) ^ 2 := by
    rw [← Real.exp_nat_mul, hfint_eq]
    congr 1
    push_cast
    ring
  calc ENNReal.ofReal (Real.exp (-(klDiv P Q).toReal))
      = ENNReal.ofReal ((Real.exp (∫ x, f x ∂P)) ^ 2) := by rw [hsq]
    _ ≤ ENNReal.ofReal ((∫ x, Real.exp (f x) ∂P) ^ 2) :=
        ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (Real.exp_pos _).le hJ 2)
    _ = (ENNReal.ofReal (∫ x, Real.exp (f x) ∂P)) ^ 2 :=
        ENNReal.ofReal_pow (integral_nonneg fun _ => (Real.exp_pos _).le) 2
    _ = (∫⁻ x, ENNReal.ofReal (Real.exp (f x)) ∂P) ^ 2 := by
        rw [ofReal_integral_eq_lintegral_ofReal hgint (ae_of_all _ fun x => (Real.exp_pos _).le)]
    _ = (∫⁻ x, r x ^ (-(2⁻¹ : ℝ)) ∂P) ^ 2 := by rw [lintegral_congr_ae hexp]
    _ = (∫⁻ ω, (P.rnDeriv ν ω * Q.rnDeriv ν ω) ^ (2⁻¹ : ℝ) ∂ν) ^ 2 := by rw [hB, hC]
