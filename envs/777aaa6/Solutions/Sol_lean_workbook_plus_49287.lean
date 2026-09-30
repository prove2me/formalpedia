-- Prove2me | solution 1 for lean_workbook_plus_49287
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T01:18:42.336567+00:00
-- url     : https://prove2.me/submissions/e6cebc67-11e0-4c35-9547-eee607fafac8

import Mathlib.Analysis.Complex.Basic

theorem solution : ∃ x y : ℤ, x^2 - 6*y^2 = 1 := ⟨5, 2, by norm_num⟩
