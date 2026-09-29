-- Prove2me | solution 1 for lean_workbook_plus_52111
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:05:05.652764+00:00
-- url     : https://prove2.me/submissions/b06f5c72-ba83-46d9-95a2-29178083a461

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : (3 * a + 3 * b) / (a ^ 2 + a * b + b ^ 2) ≥ (3 * c) / (a ^ 2 + a * c + c ^ 2) + (3 * c) / (b ^ 2 + b * c + c ^ 2) → (a ^ 2 + a * b + b ^ 2) * (3 / 4 * c ^ 2 + (a + c / 2) ^ 2) * (3 / 4 * c ^ 2 + (b + c / 2) ^ 2) ≥ (a ^ 2 + b ^ 2 + a * b) * (3 / 4 * c ^ 2 + (a + c / 2) ^ 2) * (3 / 4 * c ^ 2 + (b + c / 2) ^ 2) := by
  (intros; linarith)
