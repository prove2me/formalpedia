-- Prove2me | solution 1 for lean_workbook_plus_33525
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:06:51.578263+00:00
-- url     : https://prove2.me/submissions/66d13039-1672-4e9d-ba29-e49f0b76a91b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (h1 : a + 2 * b + 3 * c = 5) (h2 : 2 * a + 3 * b + c = -2) (h3 : 3 * a + b + 2 * c = 3) : 3 * a + 3 * b + 3 * c = 3 := by
  (intros; linarith)
