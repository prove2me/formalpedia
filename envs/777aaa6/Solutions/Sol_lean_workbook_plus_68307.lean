-- Prove2me | solution 1 for lean_workbook_plus_68307
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:20:34.709172+00:00
-- url     : https://prove2.me/submissions/199e72d1-34b9-4b25-aa1d-55854e333579

import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.NormNum

theorem solution (n : ℕ) : 6 ∣ 7^n - 1 := by
  simpa using Nat.sub_one_dvd_pow_sub_one 7 n
