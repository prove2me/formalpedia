-- Prove2me | solution 1 for lean_workbook_plus_1984
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:34:47.332787+00:00
-- url     : https://prove2.me/submissions/4391e8d7-cda4-4795-ba68-a0f858a7197b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℂ) : (c - a) * (c - b) = c^2 - a*c - b*c + a*b := by
  (intros; ring)
