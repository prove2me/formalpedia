-- Prove2me | solution 1 for lean_workbook_plus_68414
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:20:32.876269+00:00
-- url     : https://prove2.me/submissions/b1d9b1da-7313-456b-9c9f-5f60a0ce5c50

import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Ring.GeomSum

theorem solution (n k : ℕ) (hn : 1 < n) : n - 1 ∣ n^k - 1 := by
  exact Nat.sub_one_dvd_pow_sub_one n k
