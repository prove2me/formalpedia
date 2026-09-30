-- Prove2me | solution 1 for lean_workbook_plus_50112
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:33:45.258256+00:00
-- url     : https://prove2.me/submissions/78fcf5e8-be73-4ab8-8cd9-059d94deaa8d

import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Ring.GeomSum

theorem solution (a b : ℤ) (n : ℕ) : a - b ∣ a ^ n - b ^ n := by
  exact sub_dvd_pow_sub_pow a b n
