-- Prove2me | solution 1 for Hirsch.gain_normalized_column_bound
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-13T20:26:28.219061+00:00
-- url     : https://prove2.me/submissions/cb538783-2f5b-4ee3-ac6d-fb3ff75959d6

import Mathlib
set_option autoImplicit false
noncomputable section

theorem solution (x root denominator Gamma eta : ℝ)
    (hGamma : 0 ≤ Gamma) (heta : 0 < eta) (hroot : 0 < |root|)
    (htransport : |x| ≤ Gamma * |root|)
    (hgap : eta * |root| ≤ |denominator|) :
    |x / denominator| ≤ Gamma / eta := by
  have hd : 0 < |denominator| := lt_of_lt_of_le (mul_pos heta hroot) hgap
  rw [abs_div]
  apply (div_le_div_iff₀ hd heta).mpr
  have h₁ := mul_le_mul_of_nonneg_right htransport heta.le
  have h₂ := mul_le_mul_of_nonneg_left hgap hGamma
  nlinarith

#print axioms solution
