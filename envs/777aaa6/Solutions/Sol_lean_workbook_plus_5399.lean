-- Prove2me | solution 1 for lean_workbook_plus_5399
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:51:42.403087+00:00
-- url     : https://prove2.me/submissions/713d1c8b-c698-4865-887d-853eaf30dddf

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (n : ℤ) : 8 ∣ n ∧ 5 ∣ n ↔ 40 ∣ n := by
  (intros; omega)
