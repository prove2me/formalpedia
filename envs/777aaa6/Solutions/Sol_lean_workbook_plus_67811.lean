-- Prove2me | solution 1 for lean_workbook_plus_67811
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:20:33.667935+00:00
-- url     : https://prove2.me/submissions/767ccc35-a73e-4d8e-8b6c-c91b5e11ebdd

import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.NormNum

theorem solution : ∀ n : ℕ, 7 ∣ 11^n - 4^n := by
  intro n
  simpa using Nat.sub_dvd_pow_sub_pow 11 4 n
