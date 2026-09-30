-- Prove2me | solution 1 for lean_workbook_plus_81052
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:36:42.616856+00:00
-- url     : https://prove2.me/submissions/3f28cc33-c8be-49bb-9cc8-7e1b571ad5a3

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false

theorem solution (x y : ℕ) (h1 : 9*x + 12*y ≡ 4 [ZMOD 47])
    (h2 : 6*x + 7*y ≡ 14 [ZMOD 47]) : x ≡ 26 [ZMOD 47] ∧ y ≡ 20 [ZMOD 47] := by
  simp only [Int.ModEq] at *
  omega
