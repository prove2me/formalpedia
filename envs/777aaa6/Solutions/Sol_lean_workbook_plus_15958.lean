-- Prove2me | solution 1 for lean_workbook_plus_15958
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:10:07.76753+00:00
-- url     : https://prove2.me/submissions/325a32d4-4c5e-45c9-ad12-48c54c35570f

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.NormNum

theorem solution (n : ℤ) : 3 ∣ n^3 - n := by
  apply Int.dvd_iff_emod_eq_zero.mpr
  have h : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases h with h | h | h <;>
    norm_num [pow_succ, Int.sub_emod, Int.mul_emod, h]
