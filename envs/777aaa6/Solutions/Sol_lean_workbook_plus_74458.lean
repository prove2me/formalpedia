-- Prove2me | solution 1 for lean_workbook_plus_74458
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T20:16:15.557988+00:00
-- url     : https://prove2.me/submissions/d9cebd15-297f-4f80-bdc9-04eb3aa6c028

import Mathlib
set_option autoImplicit false

theorem solution (x : ℝ) (b : ℕ) (hb : b ∈ Finset.Icc 1 3) : 3 / x ≥ b → x ≤ 3 / b   := by
  intro h
  have hbNat : 1 ≤ b := (Finset.mem_Icc.mp hb).1
  have hbReal : (1 : ℝ) ≤ b := by exact_mod_cast hbNat
  have hbpos : (0 : ℝ) < b := lt_of_lt_of_le (by norm_num) hbReal
  have hxpos : 0 < x := by
    by_contra hx
    have hxnonpos : x ≤ 0 := le_of_not_gt hx
    have hquot : 3 / x ≤ 0 := div_nonpos_of_nonneg_of_nonpos (by norm_num) hxnonpos
    have hquotpos : 0 < 3 / x := lt_of_lt_of_le hbpos h
    exact (not_lt_of_ge hquot) hquotpos
  apply (le_div_iff₀ hbpos).2
  have hmul : (b : ℝ) * x ≤ 3 := (le_div_iff₀ hxpos).1 h
  simpa only [mul_comm] using hmul

#print axioms solution
