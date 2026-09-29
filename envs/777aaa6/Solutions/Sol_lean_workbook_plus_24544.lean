-- Prove2me | solution 1 for lean_workbook_plus_24544
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:19:00.200561+00:00
-- url     : https://prove2.me/submissions/6de274ff-da0b-4ba0-8530-e82e10ac0c51

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℂ) :
  (a^2*c + b^2*a + c^2*b - a^2*b - b^2*c - c^2*a) = (b - a)*(c - a)*(c - b) := by
  (intros; ring)
