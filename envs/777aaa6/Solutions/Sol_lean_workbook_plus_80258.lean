-- Prove2me | solution 1 for lean_workbook_plus_80258
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:20:27.509063+00:00
-- url     : https://prove2.me/submissions/5383d346-adc0-4c08-88d3-24416f91089c

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.NormNum

theorem solution (n : ℤ) (h₀ : Odd n) : 2 ∣ n^5 - n := by
  apply Int.dvd_iff_emod_eq_zero.mpr
  have h : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases h with h | h <;>
    norm_num [pow_succ, Int.sub_emod, Int.mul_emod, h]
