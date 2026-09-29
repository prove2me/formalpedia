-- Prove2me | solution 1 for lean_workbook_plus_16315
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:49:27.850978+00:00
-- url     : https://prove2.me/submissions/87a98b4d-6555-45db-9902-ba37bed8a7ed

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ n : ℤ, n % 2 = 1 → 7 * n ^ 2 + 5 ≡ 4 [ZMOD 8] ∧ n % 2 = 0 → n ^ 3 ≡ 0 [ZMOD 8] := by
  (intros; simp_all)
