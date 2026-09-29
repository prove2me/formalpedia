-- Prove2me | solution 1 for lean_workbook_plus_39841
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:41:13.206116+00:00
-- url     : https://prove2.me/submissions/7fafa579-8dfd-4a14-85b9-0de6c05fdac4

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ)
  (h₀ : (a + b) / 2 = 5)
  (h₁ : (b + c) / 2 = 7)
  (h₂ : (c + a) / 2 = 12) :
  a + b + c = 24 := by
  (intros; linarith)
