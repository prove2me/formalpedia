-- Prove2me | solution 1 for lean_workbook_plus_59662
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:03:13.403349+00:00
-- url     : https://prove2.me/submissions/2ee51a9b-8b2c-4ad1-b990-9b665afced19

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ x ≤ 3, 28 * x ^ 2 - 33 * x - 267 ≤ 0 := by
  decide
