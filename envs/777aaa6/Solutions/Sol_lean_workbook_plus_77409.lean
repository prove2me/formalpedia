-- Prove2me | solution 1 for lean_workbook_plus_77409
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:24:29.595415+00:00
-- url     : https://prove2.me/submissions/9aaaf054-60ca-4843-8a76-1c281a6d3a7f

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.NormNum

theorem solution (n : ℕ) (h₀ : 21 ∣ 4^(n+1)+5^(2*n-1)) :
    21 ∣ 4^(n+2)+5^(2*n+1) := by
  by_cases hn : n = 0
  · subst n
    norm_num at h₀
  have hstep : 4^(n+2)+5^(2*n+1) =
      4*(4^(n+1)+5^(2*n-1)) + 21*5^(2*n-1) := by
    rw [show n+2 = n+1+1 by omega, pow_succ,
      show 2*n+1 = 2*n-1+2 by omega, pow_add]
    norm_num
    ring
  rw [hstep]
  exact Nat.dvd_add (dvd_mul_of_dvd_right h₀ 4) (dvd_mul_right 21 _)
