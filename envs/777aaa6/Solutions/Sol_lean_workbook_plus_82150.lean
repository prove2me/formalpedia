-- Prove2me | solution 1 for lean_workbook_plus_82150
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:10:27.661956+00:00
-- url     : https://prove2.me/submissions/975b078b-334a-44d7-b298-0c00c554d07c

import Mathlib.Analysis.SpecificLimits.Basic

theorem solution (n : ℕ) (x : ℝ) (hx : 0 < x ∧ x < 1) :
    (∑' k : ℕ, x ^ (2 ^ (n + 1) * k)) = 1 / (1 - x ^ (2 ^ (n + 1))) := by
  simpa only [pow_mul, one_div] using
    tsum_geometric_of_lt_one (pow_nonneg hx.1.le _)
      (pow_lt_one₀ hx.1.le hx.2 (by positivity : 2 ^ (n + 1) ≠ 0))

#print axioms solution
