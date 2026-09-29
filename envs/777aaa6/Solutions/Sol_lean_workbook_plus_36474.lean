-- Prove2me | solution 1 for lean_workbook_plus_36474
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T02:47:58.49481+00:00
-- url     : https://prove2.me/submissions/0fdc8e85-ef51-4c07-96aa-e4a38e6ae0e4

import Mathlib

set_option autoImplicit false

namespace Workbook36474

lemma scalar_bound (t : ℝ) (ht : 0 ≤ t) :
    13 ≤ 4 * t + 25 / (t ^ 2 + 1) := by
  have hd : 0 < t ^ 2 + 1 := by positivity
  have hid : (4 * t + 25 / (t ^ 2 + 1) - 13) * (t ^ 2 + 1) =
      (t - 2) ^ 2 * (4 * t + 3) := by
    field_simp
    <;> ring
  have hp : 0 ≤ (t - 2) ^ 2 * (4 * t + 3) := by positivity
  nlinarith

-- The complete source statement, without the platform's extra abc=1 premise.
theorem full_source (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : 1 / (a ^ 2 + 1) + 2 / (b ^ 2 + 1) + 2 / (c ^ 2 + 1) = 1) :
    10 ≤ a + 2 * b + 2 * c := by
  have hsum : 25 / (a ^ 2 + 1) + 2 * (25 / (b ^ 2 + 1)) +
      2 * (25 / (c ^ 2 + 1)) = 25 := by
    linear_combination 25 * h
  have h1 := scalar_bound a ha.le
  have h2 := scalar_bound b hb.le
  have h3 := scalar_bound c hc.le
  linarith

end Workbook36474

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (_habc : a * b * c = 1) :
    1 / (a^2 + 1) + 2 / (b^2 + 1) + 2 / (c^2 + 1) = 1 →
    a + 2 * b + 2 * c ≥ 10 :=
  Workbook36474.full_source a b c ha hb hc
