-- Prove2me | solution 1 for lean_workbook_plus_16824
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:44:27.942285+00:00
-- url     : https://prove2.me/submissions/455c9dcf-7689-4b4b-8b6e-175a49709e46

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℤ) : a^3 + b^3 + c^3 - 3*a*b*c = (a + b + c)*(a^2 + b^2 + c^2 - a*b - a*c - b*c) := by
  (intros; linarith)
