-- Prove2me | solution 1 for lean_workbook_plus_13467
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:50:09.023813+00:00
-- url     : https://prove2.me/submissions/a3e09d86-d504-495f-97aa-67286d9dbbdc

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (k : ℤ) :  k ^ 3 - 1 = (k - 1) * (k ^ 2 + k + 1) → k ^ 2 + k + 1 ∣ k ^ 3 - 1 := by
  (intros; simp_all)
