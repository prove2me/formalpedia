-- Prove2me | solution 1 for zeta_zero_one_sub_of_mem_critical_strip
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-06T10:59:20.682617+00:00
-- url     : https://prove2.me/submissions/88de6e23-67a8-4fe5-b35e-7729a8ac3d0a

import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

open Complex

theorem solution (s : ℂ) (h0 : 0 < s.re) (h1 : s.re < 1)
    (hz : riemannZeta s = 0) : riemannZeta (1 - s) = 0 := by
  have hsn : ∀ n : ℕ, s ≠ -(n : ℂ) := by
    intro n hn
    have h : s.re = -(n : ℝ) := by rw [hn]; simp
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith [h ▸ h0]
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at h1
    simp at h1
  rw [riemannZeta_one_sub hsn hs1, hz, mul_zero]
