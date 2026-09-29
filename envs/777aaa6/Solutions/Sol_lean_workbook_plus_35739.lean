-- Prove2me | solution 1 for lean_workbook_plus_35739
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:17:56.53253+00:00
-- url     : https://prove2.me/submissions/74fb3653-2474-47ab-83cd-aa3e0e473c06

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ a : ℂ, (a^2 - 2) * (a^2 + 2) * (a^2 - 2 * a + 2) * (a^2 + 2 * a + 2) = a^8 - 16 := by
  (intros; ring)
