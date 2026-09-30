-- Prove2me | solution 1 for lean_workbook_plus_76682
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:57:44.359946+00:00
-- url     : https://prove2.me/submissions/d7bdd1f0-e84f-404a-a837-9c6a8b8e0820

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

private lemma cyclic_ordered (x y z : ℝ) (hz : 0 ≤ z) (hzx : z ≤ x) (hzy : z ≤ y) :
    0 ≤ 6 * (x ^ 3 + y ^ 3 + z ^ 3) +
      5 * (x ^ 2 * y + y ^ 2 * z + z ^ 2 * x) -
      11 * (x ^ 2 * z + y ^ 2 * x + z ^ 2 * y) := by
  have h1 := mul_nonneg (show 0 ≤ 6 * (x - z) by linarith)
    (sq_nonneg ((x - z) - (y - z)))
  have h2 := mul_nonneg (show 0 ≤ 17 * (y - z) by linarith)
    (sq_nonneg ((x - z) - (y - z) / 2))
  have h3 := mul_nonneg (show (0 : ℝ) ≤ 7 / 4 by norm_num)
    (pow_nonneg (sub_nonneg.mpr hzy) 3)
  have h4 := mul_nonneg (show 0 ≤ 6 * z by linarith)
    (add_nonneg (add_nonneg (sq_nonneg ((x - z) - (y - z)))
      (sq_nonneg (x - z))) (sq_nonneg (y - z)))
  nlinarith only [h1, h2, h3, h4]

private lemma cyclic_bound (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    0 ≤ 6 * (x ^ 3 + y ^ 3 + z ^ 3) +
      5 * (x ^ 2 * y + y ^ 2 * z + z ^ 2 * x) -
      11 * (x ^ 2 * z + y ^ 2 * x + z ^ 2 * y) := by
  rcases le_total z x with hzx | hxz
  · rcases le_total z y with hzy | hyz
    · exact cyclic_ordered x y z hz hzx hzy
    · nlinarith only [cyclic_ordered z x y hy hyz (hyz.trans hzx)]
  · rcases le_total x y with hxy | hyx
    · nlinarith only [cyclic_ordered y z x hx hxy hxz]
    · nlinarith only [cyclic_ordered z x y hy (hyx.trans hxz) hyx]

theorem solution (a b c : ℝ) (hx : a > 0 ∧ b > 0 ∧ c > 0)
    (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) :
    (a + b) * (b + c) * (c + a) / 8 ≥
      (2 * a + b) * (2 * b + c) * (2 * c + a) / 27 := by
  have h := cyclic_bound ((a + c - b) / 2) ((a + b - c) / 2) ((b + c - a) / 2)
    (by linarith) (by linarith) (by linarith)
  nlinarith only [h]

#print axioms solution
