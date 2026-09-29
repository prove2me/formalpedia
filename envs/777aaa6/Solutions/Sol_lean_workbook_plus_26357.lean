-- Prove2me | solution 1 for lean_workbook_plus_26357
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:18:50.107624+00:00
-- url     : https://prove2.me/submissions/dcca53e8-4db4-489b-8362-aa4544f8faea

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a r s t x : ℂ) : a * (x - r) * (x - s) * (x - t) = a * (x^3 - (r + s + t) * x^2 + (r * s + s * t + t * r) * x - r * s * t) := by
  (intros; ring)
