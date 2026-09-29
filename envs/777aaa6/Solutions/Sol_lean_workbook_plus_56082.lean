-- Prove2me | solution 1 for lean_workbook_plus_56082
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:22:24.132165+00:00
-- url     : https://prove2.me/submissions/9e66d6ba-819c-476a-9af3-6ebd2b3bc499

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ x : ℝ, ( if x ≥ 0 then 1 else -1 ) = ( if x ≥ 0 then 1 else -1 ) := by
  norm_num
