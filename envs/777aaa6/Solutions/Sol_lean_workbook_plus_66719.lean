-- Prove2me | solution 1 for lean_workbook_plus_66719
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:20:31.042994+00:00
-- url     : https://prove2.me/submissions/7a2ab827-de0a-4c16-a59a-73a28c439f3d

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c d : ℕ) (hab : a ∣ b) (hcd : c ∣ d) : a*c ∣ b*d := by
  exact Nat.mul_dvd_mul hab hcd
