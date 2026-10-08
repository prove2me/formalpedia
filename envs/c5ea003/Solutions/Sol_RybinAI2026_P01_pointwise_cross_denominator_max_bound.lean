-- Prove2me | solution 1 for RybinAI2026.P01.pointwise_cross_denominator_max_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T18:38:41.48931+00:00
-- url     : https://prove2.me/submissions/a6463dcb-96ae-4648-afb9-18db5a8eb619

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true


theorem solution
    (p q r s X Y : ℝ)
    (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) (hs : 0 < s) :
    |X + Y| / ((p + q) * (r + s)) ≤ max (|X| / (p * r)) (|Y| / (q * s)) := by
  have hpr : 0 < p * r := mul_pos hp hr
  have hqs : 0 < q * s := mul_pos hq hs
  have hD : 0 < (p + q) * (r + s) :=
    mul_pos (add_pos hp hq) (add_pos hr hs)
  have eX : (|X| / (p * r)) * (p * r) = |X| :=
    div_mul_cancel₀ _ hpr.ne'
  have eY : (|Y| / (q * s)) * (q * s) = |Y| :=
    div_mul_cancel₀ _ hqs.ne'
  have hm : 0 ≤ max (|X| / (p * r)) (|Y| / (q * s)) :=
    le_max_of_le_left (div_nonneg (abs_nonneg _) hpr.le)
  have hnum : |X| + |Y|
      ≤ max (|X| / (p * r)) (|Y| / (q * s)) * ((p * r) + (q * s)) := by
    calc |X| + |Y|
        = (|X| / (p * r)) * (p * r) + (|Y| / (q * s)) * (q * s) := by
          rw [eX, eY]
      _ ≤ max (|X| / (p * r)) (|Y| / (q * s)) * (p * r) +
          max (|X| / (p * r)) (|Y| / (q * s)) * (q * s) :=
          add_le_add
            (mul_le_mul_of_nonneg_right
              (le_max_left (|X| / (p * r)) (|Y| / (q * s))) hpr.le)
            (mul_le_mul_of_nonneg_right
              (le_max_right (|X| / (p * r)) (|Y| / (q * s))) hqs.le)
      _ = max (|X| / (p * r)) (|Y| / (q * s)) * ((p * r) + (q * s)) := by
          rw [mul_add]
  have hden : (p * r) + (q * s) ≤ (p + q) * (r + s) := by
    have h1 : 0 ≤ p * s := mul_nonneg hp.le hs.le
    have h2 : 0 ≤ q * r := mul_nonneg hq.le hr.le
    rw [add_mul, mul_add, mul_add]
    linarith
  have hfin : max (|X| / (p * r)) (|Y| / (q * s)) * ((p * r) + (q * s))
        / ((p + q) * (r + s))
      ≤ max (|X| / (p * r)) (|Y| / (q * s)) := by
    rw [div_le_iff₀ hD]
    exact mul_le_mul_of_nonneg_left hden hm
  have hcancel : ∀ a : ℝ, a / ((p + q) * (r + s)) * ((p + q) * (r + s)) = a :=
    fun a => div_mul_cancel₀ _ hD.ne'
  have hstep : ∀ a b : ℝ, a ≤ b →
      a / ((p + q) * (r + s)) ≤ b / ((p + q) * (r + s)) := by
    intro a b hab
    rw [div_le_iff₀ hD, hcancel b]
    exact hab
  calc |X + Y| / ((p + q) * (r + s))
        ≤ (|X| + |Y|) / ((p + q) * (r + s)) :=
          hstep _ _ (abs_add_le X Y)
      _ ≤ max (|X| / (p * r)) (|Y| / (q * s)) * ((p * r) + (q * s))
            / ((p + q) * (r + s)) :=
          hstep _ _ hnum
      _ ≤ max (|X| / (p * r)) (|Y| / (q * s)) := hfin
