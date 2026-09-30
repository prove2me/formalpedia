-- Prove2me | solution 1 for lean_workbook_plus_6317
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:59:05.780707+00:00
-- url     : https://prove2.me/submissions/bd191d1d-c8d7-46c6-8a4f-3e7138995e28

import Mathlib
set_option autoImplicit false

theorem solution : ∀ x : ℝ, x^8 - x^7 + x^6 + x^5 - x^3 - x^2 + 1 ≥ 0   := by
  intro x
  by_cases hlo : x ≤ -1
  · let t : ℝ := -x
    have ht : 1 ≤ t := by dsimp [t]; linarith only [hlo]
    have ht0 : 0 ≤ t := le_trans (by norm_num) ht
    have hd : 0 ≤ t-1 := sub_nonneg.mpr ht
    have hid : x^8-x^7+x^6+x^5-x^3-x^2+1 =
        t^8+t^7+t^5*(t-1)+t^2*(t-1)+1 := by dsimp [t]; ring
    rw [hid]
    exact add_nonneg
      (add_nonneg (add_nonneg (add_nonneg (pow_nonneg ht0 8) (pow_nonneg ht0 7))
        (mul_nonneg (pow_nonneg ht0 5) hd)) (mul_nonneg (pow_nonneg ht0 2) hd))
      (by norm_num)
  · by_cases hhi : 1 ≤ x
    · have hx0 : 0 ≤ x := le_trans (by norm_num) hhi
      have hd : 0 ≤ x-1 := sub_nonneg.mpr hhi
      have hcube : 1 ≤ x^3 := one_le_pow₀ hhi
      have hid : x^8-x^7+x^6+x^5-x^3-x^2+1 =
          x^7*(x-1)+(x^3+x^2)*(x^3-1)+1 := by ring
      rw [hid]
      exact add_nonneg
        (add_nonneg (mul_nonneg (pow_nonneg hx0 7) hd)
          (mul_nonneg (add_nonneg (pow_nonneg hx0 3) (sq_nonneg x))
            (sub_nonneg.mpr hcube))) (by norm_num)
    · have hl : -1 < x := lt_of_not_ge hlo
      have hu : x ≤ 1 := le_of_lt (lt_of_not_ge hhi)
      have hplus : 0 ≤ x+1 := by linarith only [hl]
      have hsquare : x^2 ≤ 1 := by
        nlinarith only [mul_nonneg hplus (sub_nonneg.mpr hu)]
      have hcube : x^3 ≤ 1 := by
        by_cases hx0 : 0 ≤ x
        · exact pow_le_one₀ hx0 hu
        · have hn : x ≤ 0 := le_of_lt (lt_of_not_ge hx0)
          calc
            x^3 = x^2*x := by ring
            _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg x) hn
            _ ≤ 1 := by norm_num
      have h6 : 0 ≤ x^6 := by
        have he : x^6 = (x^3)^2 := by ring
        rw [he]
        exact sq_nonneg _
      have hquad : 0 ≤ x^2-x+1 := by nlinarith only [sq_nonneg (x-1/2)]
      have hid : x^8-x^7+x^6+x^5-x^3-x^2+1 =
          (1-x^2)*(1-x^3)+x^6*(x^2-x+1) := by ring
      rw [hid]
      exact add_nonneg (mul_nonneg (sub_nonneg.mpr hsquare) (sub_nonneg.mpr hcube))
        (mul_nonneg h6 hquad)

#print axioms solution
