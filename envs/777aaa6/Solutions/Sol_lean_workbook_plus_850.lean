-- Prove2me | solution 1 for lean_workbook_plus_850
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:41:01.30285+00:00
-- url     : https://prove2.me/submissions/842618e0-9eb9-489a-9e35-e825b24819f1

import Mathlib.Analysis.Complex.Basic

theorem solution (a n : ℕ)
  (h₀ : Odd a)
  : Even (a^(2^n) - 1) := by
  exact Nat.Odd.sub_odd (h₀.pow) odd_one
