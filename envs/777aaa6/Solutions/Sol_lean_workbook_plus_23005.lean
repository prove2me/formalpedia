-- Prove2me | solution 1 for lean_workbook_plus_23005
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:43:23.645426+00:00
-- url     : https://prove2.me/submissions/bff2f73d-34cf-4384-abd4-14320d310703

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℤ → ℤ) (hf: f = fun x => x) : ∀ x : ℤ, f x = x := by
  (intros; simp_all)
