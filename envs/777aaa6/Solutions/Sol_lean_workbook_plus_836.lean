-- Prove2me | solution 1 for lean_workbook_plus_836
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:34:35.950296+00:00
-- url     : https://prove2.me/submissions/4ec89b9a-a4b9-4299-9be9-6697ae7ff8fe

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ a b c : ℂ, a^3 + b^3 + c^3 - 3 * a * b * c = (a + b + c) * (a^2 + b^2 + c^2 - a * b - b * c - c * a) := by
  (intros; ring)
