-- Prove2me | solution 1 for lean_workbook_plus_60536
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:41:13.392002+00:00
-- url     : https://prove2.me/submissions/54dc6c5a-7bf9-42d0-a417-6101ba342dfb

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℕ) : 1200 * x ≡ x [ZMOD 1199] := by
  (intros; simp only [Int.ModEq, Nat.ModEq] at *; omega)
