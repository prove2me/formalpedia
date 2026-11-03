-- Prove2me | Theorems.Thm_avram_chat07a_original_bv_zero_at_one_poly_residual_slope
-- name    : avram_chat07a_original_bv_zero_at_one_poly_residual_slope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T07:57:34.696204+00:00
-- url     : https://prove2.me/theorems/4a9f7c6c-b0d2-4de1-893e-1c5532e6965a
-- title:
--   avram_chat07a_original_bv_zero_at_one_poly_residual_slope
-- statement:
--   Automatically extracted helper theorem avram_chat07a_original_bv_zero_at_one_poly_residual_slope from oversized parent candidate 81315ac75da0e288ef5068268c742ccaf178f9eea9d9b72ba5aa83b531abc1a1.
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
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

theorem avram_chat07a_original_bv_zero_at_one_poly_residual_slope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (Q : Polynomial ℝ) (hQ : Polynomial.eval 1 Q = 0) :
    Tendsto (fun h : ℝ =>
      h⁻¹ * (∫ ω, Polynomial.eval
        (Real.exp (-((Real.toNNReal h : ℝ) * X.drift -
          X.X (Real.toNNReal h) ω))) Q ∂P))
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (∫ y in Iio (0 : ℝ),
        Polynomial.eval (Real.exp y) Q ∂X.ν)) := by sorry
