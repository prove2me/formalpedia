-- Prove2me | solution 1 for lean_workbook_plus_29796
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:00:37.773053+00:00
-- url     : https://prove2.me/submissions/28f461f0-6094-4a47-81b4-e383257471d3

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000


theorem solution (a b c d : ℝ) (h₁ : a * c - b * d = 8) (h₂ : a * d + b * c = 6) : (a^2 + b^2) * (c^2 + d^2) = 100 := by
  nlinarith
