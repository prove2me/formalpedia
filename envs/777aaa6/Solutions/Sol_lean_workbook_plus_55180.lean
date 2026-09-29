-- Prove2me | solution 1 for lean_workbook_plus_55180
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:03:26.973153+00:00
-- url     : https://prove2.me/submissions/41962c6a-21b1-452b-a6e3-832b4c545d8d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ z : ℂ, z^5 + z + 1 = (z^2 + z + 1) * (z^3 - z^2 + 1) := by
  (intros; ring)
