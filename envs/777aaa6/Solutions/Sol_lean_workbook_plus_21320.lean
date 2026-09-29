-- Prove2me | solution 1 for lean_workbook_plus_21320
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:19:15.516148+00:00
-- url     : https://prove2.me/submissions/e98af868-be7d-45e6-a370-a647d54d62e3

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℂ → ℂ) (hf : f = fun x : ℂ => 5 * x ^ 4 - 29 * x ^ 3 + 55 * x ^ 2 - 28 * x) : {x : ℂ | f x = 0} = {x : ℂ | 5 * x ^ 4 - 29 * x ^ 3 + 55 * x ^ 2 - 28 * x = 0} := by
  (intros; simp_all)
