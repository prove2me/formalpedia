-- Prove2me | solution 1 for lean_workbook_plus_20860
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:19:19.668826+00:00
-- url     : https://prove2.me/submissions/23668b9d-4761-4e49-be0d-4bd2a1d1af10

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (h₁ : 7^5 ≡ -1 [ZMOD 11]) : 7^130 ≡ 1 [ZMOD 11] := by
  decide
