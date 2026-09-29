-- Prove2me | solution 1 for lean_workbook_plus_79666
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-27T02:17:17.063134+00:00
-- url     : https://prove2.me/submissions/f9b5f44c-183a-42ab-8af4-b960de60b3bc

import Mathlib.Analysis.Complex.Basic

theorem solution (a : ℕ) (p : ℕ) (hp : p.Prime) (h : a < p - 1) : a + 1 < p := by
  have h2 := hp.two_le
  omega
