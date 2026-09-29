-- Prove2me | solution 1 for lean_workbook_plus_73304
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:50:43.658922+00:00
-- url     : https://prove2.me/submissions/5777ba8a-bd56-469c-a993-a73c8129f61a

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) (h : ℝ → ℝ) (hx: (x-1)/2 * h ((x-1)/2) - (1-x)/2 * h ((1-x)/2) = (x-1) * h 0) (hy: (1-x)/2 * h ((1-x)/2) - (x+1)/2 * h ((x+1)/2) = -x * h 1) (hz: (x+1)/2 * h ((x+1)/2) - (x-1)/2 * h ((x-1)/2) = h x) : h x = x * (h 1 - h 0) + h 0 := by
  (intros; linarith)
