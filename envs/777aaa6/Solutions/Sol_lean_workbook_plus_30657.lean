-- Prove2me | solution 1 for lean_workbook_plus_30657
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:54:49.496628+00:00
-- url     : https://prove2.me/submissions/1e3d12c0-9488-4e8a-bfc3-7686c55eb7db

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ c : ℝ, (5 - c) ^ 2 - 4 * (3 - 5 * c + c ^ 2) ≥ 0 ↔ -3 * (c + 1) * (c - 13 / 3) ≥ 0 := by
  (intros; ring)
