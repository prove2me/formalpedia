-- Prove2me | solution 1 for lean_workbook_plus_67976
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:53:32.809873+00:00
-- url     : https://prove2.me/submissions/fd85ef08-b638-481c-a764-fab1d310afb3

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.NormNum

theorem solution (n : ℤ) (h : n % 2 = 1) : 8 ∣ (n ^ 2 - 1) := by
  have hm : n % 8 = 1 ∨ n % 8 = 3 ∨ n % 8 = 5 ∨ n % 8 = 7 := by omega
  rcases hm with hm | hm | hm | hm
  all_goals
    apply Int.dvd_of_emod_eq_zero
    norm_num [pow_two, Int.sub_emod, Int.mul_emod, hm]

#print axioms solution
