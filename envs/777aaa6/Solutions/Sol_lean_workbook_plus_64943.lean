-- Prove2me | solution 1 for lean_workbook_plus_64943
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:06:50.834943+00:00
-- url     : https://prove2.me/submissions/54871a6f-68fc-4fa6-aedd-c6e9a8379a91

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ)
  (h₀ : x^2 = 9 / 625) :
  (2500 * (1 + x) * (1 - x) : ℝ) = 2464 := by
  (intros; linarith)
