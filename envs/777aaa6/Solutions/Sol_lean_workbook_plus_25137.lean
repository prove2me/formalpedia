-- Prove2me | solution 1 for lean_workbook_plus_25137
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T06:17:29.084452+00:00
-- url     : https://prove2.me/submissions/b9dc7aec-1613-444a-9aad-a519e1eb244f

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

def gap (x y z : ℝ) : ℝ :=
  x ^ 4 * y ^ 2 + x ^ 2 * y ^ 4 + y ^ 4 * z ^ 2 + y ^ 2 * z ^ 4 +
    z ^ 4 * x ^ 2 + z ^ 2 * x ^ 4 + 2 * (x ^ 3 * y ^ 3 + y ^ 3 * z ^ 3 + z ^ 3 * x ^ 3) -
    (2 * x * y * z * (x ^ 3 + y ^ 3 + z ^ 3) + 6 * x ^ 2 * y ^ 2 * z ^ 2)

lemma shifted_nonnegative (u v w : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w) :
    0 ≤ gap (w + u + v) (w + v) w := by
  have he : gap (w + u + v) (w + v) w =
      u ^ 4 * v ^ 2 +
      u ^ 3 * (6 * v ^ 3 + 10 * v ^ 2 * w + 6 * v * w ^ 2 + 4 * w ^ 3) +
      u ^ 2 * (13 * v ^ 4 + 40 * v ^ 3 * w + 42 * v ^ 2 * w ^ 2 + 22 * v * w ^ 3 + 8 * w ^ 4) +
      u * (12 * v ^ 5 + 50 * v ^ 4 * w + 72 * v ^ 3 * w ^ 2 + 42 * v ^ 2 * w ^ 3 + 8 * v * w ^ 4) +
      4 * v ^ 6 + 20 * v ^ 5 * w + 36 * v ^ 4 * w ^ 2 + 28 * v ^ 3 * w ^ 3 + 8 * v ^ 2 * w ^ 4 := by
    unfold gap
    ring
  rw [he]
  positivity

lemma ordered_nonnegative (x y z : ℝ) (hz : 0 ≤ z) (hzy : z ≤ y) (hyx : y ≤ x) :
    0 ≤ gap x y z := by
  have h := shifted_nonnegative (x - y) (y - z) z (sub_nonneg.2 hyx) (sub_nonneg.2 hzy) hz
  have h1 : z + (x - y) + (y - z) = x := by ring
  have h2 : z + (y - z) = y := by ring
  simpa only [h1, h2] using h

lemma nonnegative_domain (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    0 ≤ gap x y z := by
  rcases le_total x y with hxy | hyx
  · rcases le_total y z with hyz | hzy
    · have he : gap x y z = gap z y x := by unfold gap; ring
      rw [he]
      exact ordered_nonnegative z y x hx hxy hyz
    · rcases le_total x z with hxz | hzx
      · have he : gap x y z = gap y z x := by unfold gap; ring
        rw [he]
        exact ordered_nonnegative y z x hx hxz hzy
      · have he : gap x y z = gap y x z := by unfold gap; ring
        rw [he]
        exact ordered_nonnegative y x z hz hzx hxy
  · rcases le_total x z with hxz | hzx
    · have he : gap x y z = gap z x y := by unfold gap; ring
      rw [he]
      exact ordered_nonnegative z x y hy hyx hxz
    · rcases le_total y z with hyz | hzy
      · have he : gap x y z = gap x z y := by unfold gap; ring
        rw [he]
        exact ordered_nonnegative x z y hy hyz hzx
      · exact ordered_nonnegative x y z hz hzy hyx

lemma zero_sum_gap (x y z : ℝ) (h : x + y + z = 0) :
    gap x y z = -9 * (x * y * z) ^ 2 := by
  have hz : z = -x - y := by linarith
  rw [hz]
  unfold gap
  ring

theorem solution : ¬ (∀ x y z : ℝ,
    x ^ 4 * y ^ 2 + x ^ 2 * y ^ 4 + y ^ 4 * z ^ 2 + y ^ 2 * z ^ 4 +
      z ^ 4 * x ^ 2 + z ^ 2 * x ^ 4 + 2 * (x ^ 3 * y ^ 3 + y ^ 3 * z ^ 3 + z ^ 3 * x ^ 3) ≥
      2 * x * y * z * (x ^ 3 + y ^ 3 + z ^ 3) + 6 * x ^ 2 * y ^ 2 * z ^ 2) := by
  intro h
  have hg : 0 ≤ gap 1 1 (-2) := sub_nonneg.2 (h 1 1 (-2))
  have he : gap 1 1 (-2) = -36 := by unfold gap; ring
  rw [he] at hg
  norm_num at hg
