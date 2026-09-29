-- Prove2me | solution 1 for lean_workbook_plus_16614
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:49:31.782064+00:00
-- url     : https://prove2.me/submissions/610a75a4-4a9d-4912-9b76-3b290cb5b797

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ x y : ℤ, 17 ∣ 9 * x + 5 * y → 17 ∣ 2 * x + 3 * y := by
  (intros; omega)
