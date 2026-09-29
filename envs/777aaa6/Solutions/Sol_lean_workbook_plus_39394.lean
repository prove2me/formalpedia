-- Prove2me | solution 1 for lean_workbook_plus_39394
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:41:39.263129+00:00
-- url     : https://prove2.me/submissions/cb7a1f16-a478-4e1f-b254-fd1f7278d899

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (n : ℕ) : ∃ k : ℕ, (2 : ℝ)^(n+1) ∣ (1 + Real.sqrt 3)^(2 * n) - k := by
  norm_num
