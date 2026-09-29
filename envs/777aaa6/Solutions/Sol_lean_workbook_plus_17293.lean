-- Prove2me | solution 1 for lean_workbook_plus_17293
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:13:37.278715+00:00
-- url     : https://prove2.me/submissions/17ac3620-49e9-411f-9316-3e1e3a17b338

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : a ^ 2 - a * b - a * c + b ^ 2 - b * c + c ^ 2 ≥ 0 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
