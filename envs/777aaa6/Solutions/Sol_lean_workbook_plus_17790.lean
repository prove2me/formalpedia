-- Prove2me | solution 1 for lean_workbook_plus_17790
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:43:35.20469+00:00
-- url     : https://prove2.me/submissions/4ea970c5-5b74-470f-b2ec-74af9d14683b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℤ) (h : b > 0) : b ∣ a ↔ a % b = 0 := by
  (intros; omega)
