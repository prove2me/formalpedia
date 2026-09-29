-- Prove2me | solution 1 for lean_workbook_plus_4286
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:49:57.51794+00:00
-- url     : https://prove2.me/submissions/fd15a67c-a667-4539-a646-6700554ee879

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (k : ℕ) (h : 1 ≤ k) :
  (1:ℝ) / Real.sqrt (k ^ 2 + k) > (1:ℝ) / (2 * k) := by
  have hk : (1:ℝ)≤k := by exact_mod_cast h
  have hs := Real.sq_sqrt (by positivity : 0≤(k:ℝ)^2+k)
  have hp : 0<Real.sqrt ((k:ℝ)^2+k) := Real.sqrt_pos.2 (by positivity)
  have hh : Real.sqrt ((k:ℝ)^2+k) < 2*k := by nlinarith only [hs, hk, hp, sq_nonneg ((k:ℝ)-1)]
  exact one_div_lt_one_div_of_lt hp hh
