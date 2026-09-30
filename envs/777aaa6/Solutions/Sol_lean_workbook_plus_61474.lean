-- Prove2me | solution 1 for lean_workbook_plus_61474
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T22:14:45.395564+00:00
-- url     : https://prove2.me/submissions/a103fb00-4863-4192-a10e-04a5fdd352b5

import Mathlib.Analysis.Complex.Basic

theorem solution (k s : ℤ) (h₁ : 7 * k - 1 = s ^ 2) : ∃ k s, 7 * k - 1 = s ^ 2 := ⟨0, 0, by norm_num⟩
