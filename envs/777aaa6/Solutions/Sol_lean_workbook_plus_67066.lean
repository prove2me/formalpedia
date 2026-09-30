-- Prove2me | solution 1 for lean_workbook_plus_67066
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:56:06.409957+00:00
-- url     : https://prove2.me/submissions/38844d76-31f1-4a55-a425-05d6818b92f9

import Mathlib.Algebra.Ring.GeomSum

theorem solution {m n : ℕ} (hmn : m ∣ n) : 2 ^ m - 1 ∣ 2 ^ n - 1 := by
  exact Nat.pow_sub_one_dvd_pow_sub_one 2 hmn
