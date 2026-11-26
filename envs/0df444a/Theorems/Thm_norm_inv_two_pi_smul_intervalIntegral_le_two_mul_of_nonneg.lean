-- Prove2me | Theorems.Thm_norm_inv_two_pi_smul_intervalIntegral_le_two_mul_of_nonneg
-- name    : norm_inv_two_pi_smul_intervalIntegral_le_two_mul_of_nonneg
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:44:04.16615+00:00
-- url     : https://prove2.me/theorems/5a5a701f-e2da-5447-a3e0-b158f31b8c06
-- title:
--   norm inv two pi smul interval Integral le two mul of nonneg: norm inv two pi smul interval Integral le two mul of nonneg
-- statement:
--   The sharp factor-two scaling of positive-kernel contractivity for a
--   double-layer kernel with total mass `4 * pi • 1`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/DoubleLayerBound.lean#L30-L50
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/DoubleLayerBound.lean#L30-L50

import Definitions.Def_Operator_Crouzeix_DoubleLayerIntegral
import Definitions.Def_Operator_Crouzeix_PositiveKernelBound
import Definitions.Def_Operator_Crouzeix_DoubleLayerBound
set_option autoImplicit false
open MeasureTheory
open scoped InnerProductSpace Interval Real
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem norm_inv_two_pi_smul_intervalIntegral_le_two_mul_of_nonneg
    {K : ℝ → E →L[ℂ] E} {f : ℝ → ℂ} {M : ℝ}
    (hK : IntervalIntegrable K volume 0 (2 * Real.pi))
    (hfK : IntervalIntegrable (fun t ↦ f t • K t) volume 0 (2 * Real.pi))
    (hpos : ∀ t ∈ Set.Ioc (0 : ℝ) (2 * Real.pi), 0 ≤ K t)
    (hnorm : ∫ t in (0 : ℝ)..(2 * Real.pi), K t =
      (4 * Real.pi) • (1 : E →L[ℂ] E))
    (hM : 0 ≤ M) (hf : ∀ t ∈ Set.Ioc (0 : ℝ) (2 * Real.pi), ‖f t‖ ≤ M) :
    ‖(2 * Real.pi)⁻¹ • (∫ t in (0 : ℝ)..(2 * Real.pi), f t • K t)‖ ≤ 2 * M := by sorry
