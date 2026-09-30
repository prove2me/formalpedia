-- Prove2me | solution 1 for lean_workbook_plus_27480
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:16:59.562158+00:00
-- url     : https://prove2.me/submissions/982e5983-ed1d-49c9-8d43-99ea3b4deb47

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.NormNum

set_option autoImplicit false

theorem solution : ∀ n : ℤ, 6 ∣ 2 * n ^ 3 + 3 * n ^ 2 + 7 * n := by
  intro n
  have hm : n % 6 = 0 ∨ n % 6 = 1 ∨ n % 6 = 2 ∨
      n % 6 = 3 ∨ n % 6 = 4 ∨ n % 6 = 5 := by omega
  rcases hm with hm | hm | hm | hm | hm | hm
  all_goals
    apply Int.dvd_of_emod_eq_zero
    norm_num [pow_succ, Int.add_emod, Int.mul_emod, hm]

#print axioms solution
