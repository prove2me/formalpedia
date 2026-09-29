-- Prove2me | solution 1 for zeta_ne_zero_of_strip_of_six_lt_im
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-10T19:18:54.037803+00:00
-- url     : https://prove2.me/submissions/5b7cbc8d-6d0e-45c2-b2b8-b0526fe0bf00
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Theorems.Thm_moebius_summatory_rpow_bound
import Theorems.Thm_nontrivial_zero_strip_of_moebius_summatory_power_bound

open Complex

theorem solution (s : ℂ) (h0 : 1 / 2 < s.re) (h1 : s.re < 1)
    (him : 6 < s.im) : riemannZeta s ≠ 0 := by
  intro hz
  -- Choose the exponent `r = 1/2 + ε` with `ε = (Re s - 1/2)/2 > 0`, so that `r < Re s`.
  have hε : (0:ℝ) < (s.re - 1 / 2) / 2 := by linarith
  have hM := moebius_summatory_rpow_bound _ hε
  have hr : (0:ℝ) ≤ 1 / 2 + (s.re - 1 / 2) / 2 := by linarith
  -- `s` is not a trivial zero: those have negative real part.
  have hnt : ¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1) := by
    rintro ⟨n, rfl⟩
    have hre : (-2 * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by simp
    rw [hre] at h0
    have hn : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  -- `s ≠ 1` since `Im s > 6`.
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at him
    norm_num at him
  obtain ⟨-, hle⟩ :=
    nontrivial_zero_strip_of_moebius_summatory_power_bound hr hM hz hnt hs1
  linarith
