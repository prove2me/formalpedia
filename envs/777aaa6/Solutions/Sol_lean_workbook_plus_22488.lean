-- Prove2me | solution 1 for lean_workbook_plus_22488
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T20:58:15.923881+00:00
-- url     : https://prove2.me/submissions/5692b8f1-06fd-4af0-bf0a-ea54734ba126

import Mathlib
set_option autoImplicit false

theorem solution (x y : ℝ) (hxy : 0 < x ∧ 0 < y) (h : 3 = (x + y + 1) / (x * y)) : x * y ≥ 1   := by
  have hp : 0 < x * y := mul_pos hxy.1 hxy.2
  have hclear : 3 * (x * y) = x + y + 1 := (eq_div_iff hp.ne').mp h
  have hlarge : 0 < 9 * (x * y) - 1 := by nlinarith only [hclear, hxy.1, hxy.2]
  have hfactor : (x * y - 1) * (9 * (x * y) - 1) = (x - y)^2 := by
    linear_combination (3 * (x * y) + x + y - 1) * hclear
  have hnonneg : 0 <= (x * y - 1) * (9 * (x * y) - 1) := by
    rw [hfactor]
    exact sq_nonneg _
  by_contra hn
  have hnegative : (x * y - 1) * (9 * (x * y) - 1) < 0 :=
    mul_neg_of_neg_of_pos (by linarith) hlarge
  exact (not_lt_of_ge hnonneg) hnegative

#print axioms solution
