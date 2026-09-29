-- Prove2me | solution 1 for lean_workbook_plus_70233
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:01:54.076265+00:00
-- url     : https://prove2.me/submissions/6d95ee0b-7db0-427e-a144-4ecec89132e2

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ x1 x2 x3 : ℂ, 0 = x1 * x2 * x3 ^ 2 + x1 * x3 + x2 * x3 + x3 ^ 2 ↔ 0 = (x1 * x3 + 1) * (x2 * x3 + 1) + x3 ^ 2 - 1 := by
  (intros; ring)
