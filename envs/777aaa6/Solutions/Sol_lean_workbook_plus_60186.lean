-- Prove2me | solution 1 for lean_workbook_plus_60186
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:16:31.693739+00:00
-- url     : https://prove2.me/submissions/45863f11-7588-420e-9e99-3870cbbc867c

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace ReciprocalPairBound

theorem gap (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    y / x + x / y + x * y / (x + y) ^ 2 - 9 / 4 =
      (x - y) ^ 2 * ((4 * x ^ 2 + 7 * x * y + 4 * y ^ 2) /
        (4 * x * y * (x + y) ^ 2)) := by
  have hs : x + y ≠ 0 := ne_of_gt (add_pos hx hy)
  field_simp
  ring

theorem bound (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    9 / 4 ≤ y / x + x / y + x * y / (x + y) ^ 2 := by
  have h := gap x y hx hy
  have hp : 0 ≤ (x - y) ^ 2 * ((4 * x ^ 2 + 7 * x * y + 4 * y ^ 2) /
      (4 * x * y * (x + y) ^ 2)) := by positivity
  linarith

theorem equality (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    y / x + x / y + x * y / (x + y) ^ 2 = 9 / 4 ↔ x = y := by
  have hp : 0 < (4 * x ^ 2 + 7 * x * y + 4 * y ^ 2) /
      (4 * x * y * (x + y) ^ 2) := by positivity
  have hg := gap x y hx hy
  constructor
  · intro he
    have hz : (x - y) ^ 2 * ((4 * x ^ 2 + 7 * x * y + 4 * y ^ 2) /
        (4 * x * y * (x + y) ^ 2)) = 0 := by linarith
    have hs := (mul_eq_zero.mp hz).resolve_right (ne_of_gt hp)
    exact eq_of_sub_eq_zero (eq_zero_of_pow_eq_zero hs)
  · intro he
    rw [he, sub_self, zero_pow (by decide), zero_mul] at hg
    rw [he]
    linarith

end ReciprocalPairBound

theorem solution (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    (y / x + x / y + (x * y) / (x + y) ^ 2) ≥ 9 / 4 :=
  ReciprocalPairBound.bound x y hx hy
