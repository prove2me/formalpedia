-- Prove2me | solution 1 for lean_workbook_plus_82433
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:36:46.597468+00:00
-- url     : https://prove2.me/submissions/8233660a-648d-4ae3-b8f0-5fbb321cb0c3

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false

theorem solution (m n : ℤ) (h1 : m^3 - 12*m*n^2 = 40)
    (h2 : 4*n^3 - 3*m^2*n = 10) : m^2 + 4*n^2 = 14 := by
  exfalso
  have he1 := congrArg (fun x : ℤ => x % 4) h1
  have he2 := congrArg (fun x : ℤ => x % 4) h2
  simp only [pow_succ, pow_zero] at he1 he2
  have hm0 : 0 ≤ m % 4 := Int.emod_nonneg _ (by norm_num)
  have hm4 : m % 4 < 4 := Int.emod_lt_of_pos _ (by norm_num)
  have hn0 : 0 ≤ n % 4 := Int.emod_nonneg _ (by norm_num)
  have hn4 : n % 4 < 4 := Int.emod_lt_of_pos _ (by norm_num)
  interval_cases hm : m % 4 <;> interval_cases hn : n % 4 <;>
    norm_num [Int.sub_emod, Int.mul_emod, hm, hn] at he1 <;>
    norm_num [Int.sub_emod, Int.mul_emod, hm, hn] at he2
