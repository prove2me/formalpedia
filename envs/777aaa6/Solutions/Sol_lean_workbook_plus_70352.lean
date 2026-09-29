-- Prove2me | solution 1 for lean_workbook_plus_70352
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T23:51:57.757364+00:00
-- url     : https://prove2.me/submissions/c61a6b4a-bec1-494f-b031-860f7b21cc6b

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c : ℝ) (ha : a > 0) (hab : a + b + c ≥ 0) (hac : a - c ≥ 0) (hbc : a - b + c ≥ 0) : ∀ x : ℝ, a * x ^ 2 + b * x + c = 0 → abs x ≤ 1 := by
  have hupper (v t : ℝ) (hp : 0 ≤ a+v+c) (hzero : a*t^2+v*t+c=0) : t ≤ 1 := by
    by_contra hn
    have ht : 1 < t := lt_of_not_ge hn
    have hM := mul_nonneg (show 0 ≤ t by linarith) hp
    have hN := mul_nonneg (show 0 ≤ t-1 by linarith) hac
    have hP := mul_pos ha (sq_pos_of_ne_zero (show t-1 ≠ 0 by linarith))
    nlinarith only [hzero,hM,hN,hP]
  have hfull (z : ℂ) (hz : (a:ℂ)*z^2+(b:ℂ)*z+(c:ℂ)=0) : ‖z‖ ≤ 1 := by
    have hr := congrArg Complex.re hz
    have hi := congrArg Complex.im hz
    simp [pow_two, Complex.mul_re, Complex.mul_im] at hr hi
    by_cases him : z.im=0
    · have hreal : a*z.re^2+b*z.re+c=0 := by simpa [him, pow_two] using hr
      have hlow := hupper (-b) (-z.re) (by simpa only [sub_eq_add_neg] using hbc) (by nlinarith only [hreal])
      have habs : |z.re| ≤ 1 := abs_le.mpr ⟨by linarith, hupper b z.re hab hreal⟩
      calc ‖z‖ ≤ |z.re|+|z.im| := Complex.norm_le_abs_re_add_abs_im z
        _ ≤ 1 := by simpa only [him, abs_zero, add_zero] using habs
    · have he : (2*a*z.re+b)*z.im=0 := by nlinarith only [hi]
      have hb' : 2*a*z.re+b=0 := (mul_eq_zero.mp he).resolve_right him
      have hnorm : a*‖z‖^2=c := by
        rw [Complex.sq_norm, Complex.normSq_apply]
        have hm := congrArg (fun t : ℝ => t*z.re) hb'
        nlinarith only [hr,hm]
      have hs : ‖z‖^2 ≤ 1 := by
        apply (mul_le_mul_iff_right₀ ha).mp
        rw [hnorm]
        nlinarith only [hac]
      nlinarith only [hs, norm_nonneg z]
  intro x hroot
  have hz : (a:ℂ)*(x:ℂ)^2+(b:ℂ)*(x:ℂ)+(c:ℂ)=0 := by exact_mod_cast hroot
  simpa using hfull (x:ℂ) hz
