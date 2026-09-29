-- Prove2me | solution 1 for mme_strict_pow_absorbs_sqrt_exp_loss
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T02:13:15.044959+00:00
-- url     : https://prove2.me/submissions/f816d608-8da8-48e1-aded-cbd120a4ad7a

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

open Filter

set_option autoImplicit false

theorem solution
    (V B C : ℝ) (hV : 0 ≤ V) (hVB : V < B) (hC : 0 ≤ C) :
    ∀ᶠ n : ℕ in atTop,
      V ^ n ≤ B ^ n *
        Real.exp (-C * Real.sqrt (((n + 1 : ℕ) : ℝ))) := by
  have hB : 0 < B := lt_of_le_of_lt hV hVB
  rcases hV.eq_or_lt with hVzero | hVpos
  · subst V
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hn0 : n ≠ 0 := by omega
    rw [zero_pow hn0]
    positivity
  · let d : ℝ := Real.log B - Real.log V
    have hlog : Real.log V < Real.log B := Real.log_lt_log hVpos hVB
    have hd : 0 < d := sub_pos.mpr hlog
    obtain ⟨N : ℕ, hN⟩ := exists_nat_ge (1 + C ^ 2 / d ^ 2)
    filter_upwards [eventually_ge_atTop N] with n hn
    have hnR : 1 + C ^ 2 / d ^ 2 ≤ (n : ℝ) :=
      hN.trans (by exact_mod_cast hn)
    let x : ℝ := ((n + 1 : ℕ) : ℝ)
    let s : ℝ := Real.sqrt x
    have hx : 0 ≤ x := by positivity
    have hs : 0 ≤ s := Real.sqrt_nonneg _
    have hs_sq : s ^ 2 = x := by
      exact Real.sq_sqrt hx
    have hquad :
        2 * d * (C * s) ≤ d ^ 2 * x + C ^ 2 := by
      nlinarith [sq_nonneg (d * s - C)]
    have hamgm :
        C * s ≤ (d ^ 2 * x + C ^ 2) / (2 * d) := by
      exact (le_div_iff₀ (by positivity : 0 < 2 * d)).2 (by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hquad)
    have hd2 : 0 < d ^ 2 := sq_pos_of_pos hd
    have hthreshold : d ^ 2 + C ^ 2 ≤ d ^ 2 * (n : ℝ) := by
      have hmul := mul_le_mul_of_nonneg_left hnR hd2.le
      have hcancel : d ^ 2 * (1 + C ^ 2 / d ^ 2) = d ^ 2 + C ^ 2 := by
        field_simp
      rw [hcancel] at hmul
      exact hmul
    have hloss : C * s ≤ d * (n : ℝ) := by
      refine hamgm.trans ?_
      apply (div_le_iff₀ (by positivity : 0 < 2 * d)).2
      change d ^ 2 * x + C ^ 2 ≤ (d * (n : ℝ)) * (2 * d)
      dsimp [x]
      push_cast
      nlinarith
    have hexparg :
        (n : ℝ) * Real.log V ≤
          (n : ℝ) * Real.log B - C * s := by
      dsimp [d] at hloss
      nlinarith
    have hexp := Real.exp_le_exp.mpr hexparg
    have hVexp : Real.exp (Real.log V) = V := Real.exp_log hVpos
    have hBexp : Real.exp (Real.log B) = B := Real.exp_log hB
    rw [Real.exp_sub, Real.exp_nat_mul, hVexp,
      Real.exp_nat_mul, hBexp] at hexp
    rw [div_eq_mul_inv, ← Real.exp_neg] at hexp
    simpa [s, x] using hexp
