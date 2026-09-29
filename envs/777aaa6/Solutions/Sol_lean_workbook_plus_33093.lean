-- Prove2me | solution 1 for lean_workbook_plus_33093
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:38:55.13239+00:00
-- url     : https://prove2.me/submissions/281570bd-f939-425e-b3cb-3abc97a64b9e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution :  ∀ k : ℤ, (k^3 - k) * (k + 2) = k^4 + 2 * k^3 - k^2 - 2 * k := by
  (intros; linarith)
