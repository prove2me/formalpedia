-- Prove2me | solution 1 for lean_workbook_plus_59411
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:32:45.393046+00:00
-- url     : https://prove2.me/submissions/6e37314c-7306-48b7-9a30-d8642160845b

import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.NormNum

theorem solution (n : ℕ) : 11 ∣ (10^n + (-1 : ℤ)^(n + 1)) := by
  simpa [pow_succ] using sub_dvd_pow_sub_pow (10 : ℤ) (-1) n

#print axioms solution
