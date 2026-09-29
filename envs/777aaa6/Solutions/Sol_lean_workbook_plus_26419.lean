-- Prove2me | solution 1 for lean_workbook_plus_26419
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:18:46.968744+00:00
-- url     : https://prove2.me/submissions/8c3e3322-63d2-4a1a-a399-3d22b9a98309

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ x : ℂ, x^7 + 1 = (x + 1) * (x^6 - x^5 + x^4 - x^3 + x^2 - x + 1) := by
  (intros; ring)
