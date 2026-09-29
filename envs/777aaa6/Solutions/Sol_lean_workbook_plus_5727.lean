-- Prove2me | solution 1 for lean_workbook_plus_5727
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T23:41:14.818509+00:00
-- url     : https://prove2.me/submissions/7831312d-9b1d-4493-9a63-3e60ae476376

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c α β γ : ℝ) (hx: a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) (hα: α = (b + c) / a) (hβ: β = (c + a) / b) (hγ: γ = (a + b) / c) : (α + β + γ + 2 = α * β * γ ∧ 2 * (α + β + γ) ≤ α * β + β * γ + γ * α) := by
  rcases hx with ⟨ha,hb,hc⟩
  clear hab hbc hca
  subst α
  subst β
  subst γ
  have hsorted (x y z : ℝ) (hz : 0 ≤ z) (hzy : z ≤ y) (hyx : y ≤ x) :
      0 ≤ x^3+y^3+z^3+3*x*y*z-(x^2*y+x*y^2+y^2*z+y*z^2+z^2*x+z*x^2) := by
    have hy : 0 ≤ y := le_trans hz hzy
    have hxz : z ≤ x := le_trans hzy hyx
    have hcoef : 0 ≤ x+y-z := by linarith
    have ht := mul_nonneg (mul_nonneg hz (sub_nonneg.mpr hxz)) (sub_nonneg.mpr hzy)
    nlinarith only [mul_nonneg (sq_nonneg (x-y)) hcoef, ht]
  have hS : 0 ≤ a^3+b^3+c^3+3*a*b*c-(a^2*b+a*b^2+b^2*c+b*c^2+c^2*a+c*a^2) := by
    rcases le_total a b with hab | hba
    · rcases le_total b c with hbc | hcb
      · nlinarith only [hsorted c b a (le_of_lt ha) hab hbc]
      · rcases le_total a c with hac | hca
        · nlinarith only [hsorted b c a (le_of_lt ha) hac hcb]
        · nlinarith only [hsorted b a c (le_of_lt hc) hca hab]
    · rcases le_total a c with hac | hca
      · nlinarith only [hsorted c a b (le_of_lt hb) hba hac]
      · rcases le_total b c with hbc | hcb
        · nlinarith only [hsorted a c b (le_of_lt hb) hbc hca]
        · nlinarith only [hsorted a b c (le_of_lt hc) hcb hba]
  constructor
  · field_simp [ne_of_gt ha, ne_of_gt hb, ne_of_gt hc] <;> ring
  · have hd : 0 < a*b*c := by positivity
    have he : (((b+c)/a*((c+a)/b)+(c+a)/b*((a+b)/c)+(a+b)/c*((b+c)/a))-2*((b+c)/a+(c+a)/b+(a+b)/c))*(a*b*c) = a^3+b^3+c^3+3*a*b*c-(a^2*b+a*b^2+b^2*c+b*c^2+c^2*a+c*a^2) := by
      field_simp [ne_of_gt ha, ne_of_gt hb, ne_of_gt hc] <;> ring
    have hg : 0 ≤ (((b+c)/a*((c+a)/b)+(c+a)/b*((a+b)/c)+(a+b)/c*((b+c)/a))-2*((b+c)/a+(c+a)/b+(a+b)/c)) := by
      apply (mul_nonneg_iff_of_pos_right hd).mp
      rw [he]
      exact hS
    linarith
