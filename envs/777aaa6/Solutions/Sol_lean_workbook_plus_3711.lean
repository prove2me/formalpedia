-- Prove2me | solution 1 for lean_workbook_plus_3711
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:52:51.358047+00:00
-- url     : https://prove2.me/submissions/c1c1e6a5-4be0-4351-ab04-292bb10e4708

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

theorem solution (f : ℝ → ℝ) (hf : ∀ x, f (f x) = x^2 + 1/4) :
    f (1/2) = 1/2 := by
  have hh : f (f (1/2)) = 1/2 := by nlinarith only [hf (1/2)]
  have ht := hf (f (1/2))
  rw [hh] at ht
  have hs : (f (1/2) - 1/2)^2 = 0 := by nlinarith only [ht]
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hs)
