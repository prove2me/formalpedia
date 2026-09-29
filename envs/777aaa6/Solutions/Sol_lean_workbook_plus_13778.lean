-- Prove2me | solution 1 for lean_workbook_plus_13778
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:38:41.68545+00:00
-- url     : https://prove2.me/submissions/603b06c3-bccb-4a07-8422-1cd3f7bb260b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) : (a^2 - b)^2 * (a^2 + b)^2 ≥ 0 := by
  (intros; positivity)
