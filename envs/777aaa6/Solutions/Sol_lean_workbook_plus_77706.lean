-- Prove2me | solution 1 for lean_workbook_plus_77706
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:55:20.516305+00:00
-- url     : https://prove2.me/submissions/0636d060-b6dd-4591-bf13-3c69358a42fb

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

private lemma schur_ordered (a b c : ℝ) (hc : 0 ≤ c) (hab : b ≤ a) (hbc : c ≤ b) :
    a ^ 3 + b ^ 3 + c ^ 3 + 3 * a * b * c ≥
      a ^ 2 * b + b ^ 2 * c + c ^ 2 * a + a ^ 2 * c + b ^ 2 * a + c ^ 2 * b := by
  have h1 := mul_nonneg (sq_nonneg (a - b)) (show 0 ≤ a + b - c by linarith)
  have h2 := mul_nonneg hc
    (mul_nonneg (sub_nonneg.mpr (hbc.trans hab)) (sub_nonneg.mpr hbc))
  nlinarith

private lemma schur (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    a ^ 3 + b ^ 3 + c ^ 3 + 3 * a * b * c ≥
      a ^ 2 * b + b ^ 2 * c + c ^ 2 * a + a ^ 2 * c + b ^ 2 * a + c ^ 2 * b := by
  rcases le_total a b with hab | hba
  · rcases le_total b c with hbc | hcb
    · nlinarith [schur_ordered c b a ha hbc hab]
    · rcases le_total a c with hac | hca
      · nlinarith [schur_ordered b c a ha hcb hac]
      · nlinarith [schur_ordered b a c hc hab hca]
  · rcases le_total a c with hac | hca
    · nlinarith [schur_ordered c a b hb hac hba]
    · rcases le_total b c with hbc | hcb
      · nlinarith [schur_ordered a c b hb hca hbc]
      · exact schur_ordered a b c hc hba hcb

private lemma cyclic_ordered (x y z : ℝ) (hx : 0 ≤ x) (hxz : x ≤ z) :
    3 * x * y * z ≤ x ^ 2 * y + y ^ 2 * z + z ^ 2 * x := by
  have h1 := mul_nonneg hx
    (add_nonneg (add_nonneg (sq_nonneg (y - z)) (sq_nonneg (y - x)))
      (sq_nonneg (z - x)))
  have h2 := mul_nonneg (sq_nonneg (y - x)) (sub_nonneg.mpr hxz)
  nlinarith

private lemma cyclic_amgm (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    3 * x * y * z ≤ x ^ 2 * y + y ^ 2 * z + z ^ 2 * x := by
  rcases le_total x z with hxz | hzx
  · exact cyclic_ordered x y z hx hxz
  · rcases le_total z y with hzy | hyz
    · nlinarith [cyclic_ordered z x y hz hzy]
    · nlinarith [cyclic_ordered y z x hy (hyz.trans hzx)]

theorem solution (x y z : ℝ) (hx : x ≥ 0) (hy : y ≥ 0) (hz : z ≥ 0) :
    (x + 2 * y + z) * (y + 2 * z + x) * (z + 2 * x + y) ≥
      (3 * x + z) * (3 * y + x) * (3 * z + y) := by
  nlinarith only [schur x y z hx hy hz, cyclic_amgm x y z hx hy hz]

#print axioms solution
