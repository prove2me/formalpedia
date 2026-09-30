-- Prove2me | solution 1 for lean_workbook_plus_3415
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:52:52.161426+00:00
-- url     : https://prove2.me/submissions/45fcf722-1696-4937-9c98-9306d4fe9f0f

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

private theorem complement (f : ℝ → ℝ) (hf : ∀ x, f (f x) = 1 - x)
    (x : ℝ) : f (1 - x) = 1 - f x := by
  calc
    f (1 - x) = f (f (f x)) := congrArg f (hf x).symm
    _ = 1 - f x := hf (f x)

theorem solution (f : ℝ → ℝ) (hf : ∀ x, f (f x) = 1 - x) :
    f (1 / 4) + f (3 / 4) = 1 := by
  have h := complement f hf (1/4)
  rw [show (1 : ℝ) - 1/4 = 3/4 by ring] at h
  linarith only [h]
