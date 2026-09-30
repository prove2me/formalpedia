-- Prove2me | solution 1 for lean_workbook_plus_42414
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T21:07:21.362961+00:00
-- url     : https://prove2.me/submissions/abc44028-5923-42c6-9da9-023d77621a80

import Mathlib.Analysis.Complex.Basic

theorem solution : ∃ a b c : ℤ, a + b + c = 9 := ⟨9, 0, 0, by norm_num⟩
