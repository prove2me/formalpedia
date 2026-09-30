-- Prove2me | solution 1 for lean_workbook_plus_27684
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T05:41:44.915537+00:00
-- url     : https://prove2.me/submissions/f6d0b6e9-b724-42e1-8e9e-7f558677eed3

import Mathlib

set_option autoImplicit false

theorem nonnegative_parameter (r : Real) (hr : 0 ≤ r) :
    2 / (1 + r + r ^ 2 + r ^ 3) ≥ 1 / (1 + r ^ 3) := by
  have h1 : 1 + r + r ^ 2 + r ^ 3 ≠ 0 := by positivity
  have h2 : 1 + r ^ 3 ≠ 0 := by positivity
  have hid : 2 / (1 + r + r ^ 2 + r ^ 3) - 1 / (1 + r ^ 3) =
      (r - 1) ^ 2 * (r + 1) / ((1 + r + r ^ 2 + r ^ 3) * (1 + r ^ 3)) := by
    field_simp
    ring
  have hn : 0 ≤ (r - 1) ^ 2 * (r + 1) := by positivity
  have hd : 0 < (1 + r + r ^ 2 + r ^ 3) * (1 + r ^ 3) := by positivity
  have hdiff : 0 ≤ 2 / (1 + r + r ^ 2 + r ^ 3) - 1 / (1 + r ^ 3) := by
    rw [hid]
    exact div_nonneg hn hd.le
  linarith

theorem solution : ¬ (∀ r : Real,
    2 / (1 + r + r ^ 2 + r ^ 3) ≥ 1 / (1 + r ^ 3)) := by
  intro h
  have hc := h (-2)
  norm_num at hc

#print axioms solution
