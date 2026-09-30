-- Prove2me | solution 1 for lean_workbook_plus_43714
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:54:50.903586+00:00
-- url     : https://prove2.me/submissions/bb25bca4-5c8c-4653-a4e7-1557d888993a

import Mathlib.Analysis.Complex.Basic

theorem solution (n : ℕ) : ∃ q r : ℕ, 0 ≤ r ∧ r < 3 ∧ n = 3 * q + r := by
  refine ⟨n / 3, n % 3, Nat.zero_le _, Nat.mod_lt _ (by norm_num), ?_⟩
  exact (Nat.div_add_mod n 3).symm
