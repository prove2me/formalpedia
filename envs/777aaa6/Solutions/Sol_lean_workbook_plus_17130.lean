-- Prove2me | solution 1 for lean_workbook_plus_17130
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:19:26.013461+00:00
-- url     : https://prove2.me/submissions/665c9f7c-a95f-46ec-ab18-80b43e3d5446

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ z1 z2 : ℂ, (z1 + z2) * (z1 + 1) * (z2 + 1) + z1 * z2 = 0 ↔ (z1 + z2) ^ 2 + (z1 + z2) * (z1 * z2) + (z1 + z2) + (z1 * z2) = 0 := by
  (intros; ring)
