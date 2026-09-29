-- Prove2me | solution 1 for riemann_hypothesis_imp_zeta_ne_zero_of_half_lt_re
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-06T11:06:26.046999+00:00
-- url     : https://prove2.me/submissions/605b23fd-9e39-49e7-ae6e-e841fa24f3f8

import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Nonvanishing

open Complex

theorem solution (h : RiemannHypothesis) (s : ℂ) (hs : 1 / 2 < s.re) : riemannZeta s ≠ 0 := by
  intro hz
  have hs1 : s ≠ 1 := by
    rintro rfl
    exact riemannZeta_ne_zero_of_one_le_re (by simp) hz
  have htriv : ¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1) := by
    rintro ⟨n, rfl⟩
    simp only [Complex.mul_re, Complex.add_re, Complex.natCast_re, Complex.one_re,
      Complex.add_im, Complex.natCast_im, Complex.one_im] at hs
    norm_num at hs
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have := h s hz htriv hs1
  linarith
