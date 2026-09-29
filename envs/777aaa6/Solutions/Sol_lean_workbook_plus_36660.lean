-- Prove2me | solution 1 for lean_workbook_plus_36660
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T02:49:12.755555+00:00
-- url     : https://prove2.me/submissions/0f4cef7f-e419-47c0-8e49-4de3501c7e70

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false

private lemma reciprocal_sum_lower_bound (x y z : ℝ)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    3 / 2 ≤ x / (y + z) + y / (z + x) + z / (x + y) := by
  have hxy : x + y ≠ 0 := ne_of_gt (by positivity)
  have hyz : y + z ≠ 0 := ne_of_gt (by positivity)
  have hzx : z + x ≠ 0 := ne_of_gt (by positivity)
  let N := (x-y)^2*(x+y)+(y-z)^2*(y+z)+(z-x)^2*(z+x)
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hid : x/(y+z)+y/(z+x)+z/(x+y)-3/2 =
      N / (2*(x+y)*(y+z)*(z+x)) := by
    dsimp [N]
    field_simp [hxy, hyz, hzx]
    ring
  have hh := div_nonneg hN (show 0 ≤ 2*(x+y)*(y+z)*(z+x) by positivity)
  rw [← hid] at hh
  linarith

private lemma full_source (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : 1 / (a^2*(b+c)) + 1 / (b^2*(a+c)) + 1 / (c^2*(a+b)) = 1) :
    a*b*c ≥ 3/2 := by
  have ha' : a ≠ 0 := ne_of_gt ha
  have hb' : b ≠ 0 := ne_of_gt hb
  have hc' : c ≠ 0 := ne_of_gt hc
  have hab : a+b ≠ 0 := ne_of_gt (by positivity)
  have hac : a+c ≠ 0 := ne_of_gt (by positivity)
  have hbc : b+c ≠ 0 := ne_of_gt (by positivity)
  have habi : 1/a+1/b ≠ 0 := ne_of_gt (by positivity)
  have hbci : 1/b+1/c ≠ 0 := ne_of_gt (by positivity)
  have hcai : 1/c+1/a ≠ 0 := ne_of_gt (by positivity)
  have he : a*b*c = (1/a)/(1/b+1/c)+(1/b)/(1/c+1/a)+(1/c)/(1/a+1/b) := by
    calc
      a*b*c = a*b*c*(1/(a^2*(b+c))+1/(b^2*(a+c))+1/(c^2*(a+b))) := by rw [h]; ring
      _ = (1/a)/(1/b+1/c)+(1/b)/(1/c+1/a)+(1/c)/(1/a+1/b) := by
        field_simp [ha', hb', hc', hab, hac, hbc, habi, hbci, hcai]
        ring
  rw [he]
  exact reciprocal_sum_lower_bound (1/a) (1/b) (1/c) (by positivity) (by positivity) (by positivity)

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : (1 / (a^2 * (b + c)) + 1 / (b^2 * (a + c)) + 1 / (c^2 * (a + b))) = 1) : a * b * c ≥ 3 / 2   := by
  exact full_source a b c ha hb hc h
