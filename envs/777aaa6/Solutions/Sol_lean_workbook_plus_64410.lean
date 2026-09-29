-- Prove2me | solution 1 for lean_workbook_plus_64410
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T02:27:20.166549+00:00
-- url     : https://prove2.me/submissions/adb3fd0a-47d9-488f-8d8d-46ebbebd9ff2

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hab : a + b ≠ 0) (hbc : b + c ≠ 0) (hca : a + c ≠ 0) : (a^2 / (a + b) + b^2 / (b + c) + c^2 / (c + a) ≤ (3 * (a^2 + b^2 + c^2)) / (2 * (a + b + c))) ↔ (a^3 * b^2 + b^3 * c^2 + c^3 * a^2 + a^2 * b^3 + b^2 * c^3 + c^2 * a^3 ≤ a^4 * b + b^4 * c + c^4 * a + a * b^4 + b * c^4 + c * a^4)   := by
  have habp : 0 < a + b := lt_of_le_of_ne (add_nonneg ha hb) (Ne.symm hab)
  have hbcp : 0 < b + c := lt_of_le_of_ne (add_nonneg hb hc) (Ne.symm hbc)
  have hcap : 0 < c + a := by
    simpa [add_comm] using lt_of_le_of_ne (add_nonneg ha hc) (Ne.symm hca)
  have hsum : 0 < a + b + c := add_pos_of_pos_of_nonneg habp hc
  have hd : 0 < 2 * (a + b + c) * (a + b) * (b + c) * (c + a) := by positivity
  have hid :
      (3 * (a^2 + b^2 + c^2)) / (2 * (a + b + c)) -
        (a^2 / (a + b) + b^2 / (b + c) + c^2 / (c + a)) =
      (a^4 * b + b^4 * c + c^4 * a + a * b^4 + b * c^4 + c * a^4 -
        (a^3 * b^2 + b^3 * c^2 + c^3 * a^2 + a^2 * b^3 + b^2 * c^3 + c^2 * a^3)) /
      (2 * (a + b + c) * (a + b) * (b + c) * (c + a)) := by
    field_simp [ne_of_gt hsum, ne_of_gt habp, ne_of_gt hbcp, ne_of_gt hcap]
    <;> ring
  have hright : a^3 * b^2 + b^3 * c^2 + c^3 * a^2 + a^2 * b^3 + b^2 * c^3 + c^2 * a^3 ≤
      a^4 * b + b^4 * c + c^4 * a + a * b^4 + b * c^4 + c * a^4 := by
    have hnonneg : 0 ≤ a * b * (a - b)^2 * (a + b) +
        b * c * (b - c)^2 * (b + c) + c * a * (c - a)^2 * (c + a) := by positivity
    nlinarith only [hnonneg]
  apply iff_of_true ?_ hright
  rw [← sub_nonneg, hid, le_div_iff₀ hd, zero_mul, sub_nonneg]
  exact hright
