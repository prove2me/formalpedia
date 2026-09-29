-- Prove2me | solution 1 for lean_workbook_plus_16365
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:49:05.394743+00:00
-- url     : https://prove2.me/submissions/b543c1ff-6af1-490e-9dff-afab509b28a9

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ a b c : ℤ, a * b * c = b * c * a → a^3 * (b - c) + b^3 * (c - a) + c^3 * (a - b) = (b - a) * (c * (b^2 + b * a + a^2) - b * a * (b + a) - c^3) := by
  (intros; linarith)
