-- Prove2me | solution 1 for BookSixth.latin_upper_factor_ge_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T00:12:58.024885+00:00
-- url     : https://prove2.me/submissions/a6a64d2f-3d2c-4daa-94c1-388253b0d8e4

import Mathlib
import Definitions.Def_BookSixth

open scoped BigOperators
open BookSixth

theorem solution (n k : ℕ) (hk : 1 ≤ k) :
    1 ≤ (k.factorial : ℝ) ^ ((n : ℝ) / (k : ℝ)) := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hbase : (1 : ℝ) ≤ k.factorial := by
    have h : 1 ≤ k.factorial := Nat.factorial_pos k
    exact_mod_cast h
  have hexp : (0 : ℝ) ≤ (n : ℝ) / (k : ℝ) := by
    apply div_nonneg (Nat.cast_nonneg _) (le_trans zero_le_one hkR)
  exact Real.one_le_rpow hbase hexp
