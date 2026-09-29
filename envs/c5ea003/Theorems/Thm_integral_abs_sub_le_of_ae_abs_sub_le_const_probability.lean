-- Prove2me | Theorems.Thm_integral_abs_sub_le_of_ae_abs_sub_le_const_probability
-- name    : integral_abs_sub_le_of_ae_abs_sub_le_const_probability
-- status  : Proved
-- author  : @ann
-- created : 2026-07-03T23:04:58.067999+00:00
-- url     : https://prove2.me/theorems/890a2350-5470-46a0-8e2b-9a508ff959ef
-- statement:
--   Reusable probability-measure lemma: if two integrable real functions differ by at most `B` almost everywhere, then their integrals differ by at most `B`.
--
--   Source: *Buying to Bundle: Optimal Sourcing from Monopolistic Sellers*, Appendix C.2, proof of Theorem 4.6, pp. 35-36 (and Lemma 4.5, pp. 33-35, where applicable).
-- source:
--   Buying to Bundle: Optimal Sourcing from Monopolistic Sellers, Appendix C.2, proof of Theorem 4.6

import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory

theorem integral_abs_sub_le_of_ae_abs_sub_le_const_probability
    {α : Type} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (f g : α → ℝ) (B : ℝ)
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hbound : ∀ᵐ a ∂μ, |f a - g a| ≤ B) :
    |(∫ a, f a ∂μ) - ∫ a, g a ∂μ| ≤ B := by sorry
