-- Prove2me | solution 1 for BookSixth.latin_upper_prod_ge_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T00:17:57.279639+00:00
-- url     : https://prove2.me/submissions/3fd3e1c9-fbc4-4462-96bd-b8722a19ee4d

import Mathlib
import Definitions.Def_BookSixth

open scoped BigOperators
open BookSixth

theorem factor_ge_one (n k : ℕ) (hk : 1 ≤ k) :
    1 ≤ (k.factorial : ℝ) ^ ((n : ℝ) / (k : ℝ)) := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hbase : (1 : ℝ) ≤ k.factorial := by
    have h : 1 ≤ k.factorial := Nat.factorial_pos k
    exact_mod_cast h
  have hexp : (0 : ℝ) ≤ (n : ℝ) / (k : ℝ) := by
    apply div_nonneg (Nat.cast_nonneg _) (le_trans zero_le_one hkR)
  exact Real.one_le_rpow hbase hexp

theorem solution (n : ℕ) :
    1 ≤ ∏ k ∈ Finset.Icc 1 n, (k.factorial : ℝ) ^ ((n : ℝ) / (k : ℝ)) := by
  have h1 : (∏ k ∈ Finset.Icc 1 n, (1 : ℝ)) = 1 := by simp
  rw [← h1]
  apply Finset.prod_le_prod
  · intro k hk
    positivity
  · intro k hk
    exact le_of_eq (by simp) |>.trans (factor_ge_one n k (Finset.mem_Icc.mp hk).1)
