-- Prove2me | Theorems.Thm_avram_chat07a_residual_limit_assembly
-- name    : avram_chat07a_residual_limit_assembly
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T08:36:51.872229+00:00
-- url     : https://prove2.me/theorems/de490764-4d83-4862-be3f-1e431459626b
-- title:
--   avram_chat07a_residual_limit_assembly
-- statement:
--   Automatically extracted helper theorem avram_chat07a_residual_limit_assembly from oversized parent candidate 81315ac75da0e288ef5068268c742ccaf178f9eea9d9b72ba5aa83b531abc1a1.
-- source:
--   candidate-decomposition:b56e7174-ebfe-49ac-899d-0f14fc900201:81315ac75da0e288ef5068268c742ccaf178f9eea9d9b72ba5aa83b531abc1a1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_endpoint_zero_poly_as_exponential_primitive
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_zero_poly_primitive_right_slope
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_zero_poly_primitive_levy_integral
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_integrable_signed_negative_jump_tail_DCT
import Theorems.Thm_AvramDividend_Classical_boundedVariation_full_negative_jump_increment_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_residual_normalized_tail_uniform_vanish
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_C1_joint_residual_levy_poly_choice
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_BV_original_residual_poly_error_normalized
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_residual_normalized_mean_le_two_terminal_mean
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_BV_endpoint_poly_levy_integrable
import Theorems.Thm_AvramDividend_Classical_bv_exponential_jump_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_signed_payoff_BV_Levy_L1_error_transfer
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_global_C1_lipschitz_transition_integrable_upto_one
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_poly_residual_primitive_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_original_C1_source_drift_expectation_right_slope
import Theorems.Thm_AvramDividend_Classical_boundedVariation_generator_physical_drift_representation
import Theorems.Thm_avram_chat07a_tendsto_approx
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

theorem avram_chat07a_residual_limit_assembly
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (L x : ℝ)
    (hF : ∀ t : ℝ≥0, t ≤ (1 / 2 : ℝ≥0) →
      Integrable (fun ω =>
        w x - w (x - ((t : ℝ) * X.drift - X.X t ω))) P)
    (hPoly : ∀ Q : Polynomial ℝ, Polynomial.eval 1 Q = 0 →
      ∀ t : ℝ≥0,
        Integrable (fun ω => Polynomial.eval
          (Real.exp (-((t : ℝ) * X.drift - X.X t ω))) Q) P)
    (hSlope : ∀ Q : Polynomial ℝ, Polynomial.eval 1 Q = 0 →
      Tendsto (fun h : ℝ => h⁻¹ *
        (∫ ω, Polynomial.eval
          (Real.exp (-((Real.toNNReal h : ℝ) * X.drift -
            X.X (Real.toNNReal h) ω))) Q ∂P))
        (nhdsWithin (0 : ℝ) (Ioi 0))
        (nhds (∫ y in Iio (0 : ℝ),
          Polynomial.eval (Real.exp y) Q ∂X.ν)))
    (hJoint : ∀ η : ℝ, 0 < η →
      ∃ Q : Polynomial ℝ, Polynomial.eval 1 Q = 0 ∧
        (∀ t : ℝ≥0, 0 < t → t ≤ (1 / 2 : ℝ≥0) →
          |(t : ℝ)⁻¹ * (∫ ω,
            (w x - w (x - ((t : ℝ) * X.drift - X.X t ω))) -
            Polynomial.eval (Real.exp (-((t : ℝ) * X.drift -
              X.X t ω))) Q ∂P)| ≤
            η * (2 * (∫ ω, (1 : ℝ) * X.drift -
              X.X 1 ω ∂P) + 2 * L)) ∧
        |(∫ y in Iio (0 : ℝ), Polynomial.eval (Real.exp y) Q ∂X.ν) -
          (∫ y in Iio (0 : ℝ), w x - w (x + y) ∂X.ν)| ≤
          η * ((∫ y in Iio (0 : ℝ), 1 - Real.exp y ∂X.ν) + 2)) :
    Tendsto
      (fun h : ℝ => h⁻¹ * (∫ ω,
        w x - w (x - ((Real.toNNReal h : ℝ) * X.drift -
          X.X (Real.toNNReal h) ω)) ∂P))
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (∫ y in Iio (0 : ℝ), w x - w (x + y) ∂X.ν)) := by sorry
