-- Prove2me | solution 1 for lean_workbook_plus_42638
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:16:37.555225+00:00
-- url     : https://prove2.me/submissions/f0289c79-014b-434b-8246-32138ed019bb

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ x : ℂ, x^13 + x + 90 = (x^11 + x^10 - x^9 - 3*x^8 - x^7 + 5*x^6 + 7*x^5 - 3*x^4 - 17*x^3 - 11*x^2 + 23*x + 45) * (x^2 - x + 2) := by
  (intros; ring)
