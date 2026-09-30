-- Prove2me | solution 2 for lean_workbook_plus_50112
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:41:24.992546+00:00
-- url     : https://prove2.me/submissions/f89045d3-99bf-457e-8d6f-ac5c3653e72a

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℤ) (n : ℕ) : a - b ∣ a ^ n - b ^ n := by
  (intros; exact sub_dvd_pow_sub_pow _ _ _)
