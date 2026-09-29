-- Prove2me | solution 1 for lean_workbook_plus_36033
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:17:17.506907+00:00
-- url     : https://prove2.me/submissions/a2ad365e-2507-4a65-8357-5628f114df73

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution {a b c : ℂ} : (a + b + c) ^ 5 - a ^ 5 - b ^ 5 - c ^ 5 = 5 * (a + b) * (b + c) * (c + a) * (a ^ 2 + b ^ 2 + c ^ 2 + a * b + b * c + c * a) := by
  (intros; ring)
