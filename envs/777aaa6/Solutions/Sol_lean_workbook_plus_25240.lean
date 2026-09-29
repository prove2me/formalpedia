-- Prove2me | solution 1 for lean_workbook_plus_25240
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T02:51:10.263148+00:00
-- url     : https://prove2.me/submissions/4b1d37ea-595d-48aa-85df-69f0ebbe54a8

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false

private theorem schur_ordered (a b c : ℝ) (hc : 0 ≤ c) (hcb : c ≤ b) (hba : b ≤ a) :
    0 ≤ a^3 + b^3 + c^3 + 3*a*b*c -
      (a^2*b + a*b^2 + b^2*c + b*c^2 + c^2*a + c*a^2) := by
  have hsum : 0 ≤ a + b - c := by linarith
  have hprod : 0 ≤ (a-b)^2 * (a+b-c) + c*(a-c)*(b-c) := by
    exact add_nonneg (mul_nonneg (sq_nonneg _) hsum)
      (mul_nonneg (mul_nonneg hc (sub_nonneg.mpr (hcb.trans hba))) (sub_nonneg.mpr hcb))
  nlinarith only [hprod]

private theorem schur_three (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    0 ≤ a^3 + b^3 + c^3 + 3*a*b*c -
      (a^2*b + a*b^2 + b^2*c + b*c^2 + c^2*a + c*a^2) := by
  rcases le_total a b with hab | hba
  · rcases le_total b c with hbc | hcb
    · nlinarith only [schur_ordered c b a ha hab hbc]
    · rcases le_total a c with hac | hca
      · nlinarith only [schur_ordered b c a ha hac hcb]
      · nlinarith only [schur_ordered b a c hc hca hab]
  · rcases le_total a c with hac | hca
    · nlinarith only [schur_ordered c a b hb hba hac]
    · rcases le_total b c with hbc | hcb
      · nlinarith only [schur_ordered a c b hb hbc hca]
      · exact schur_ordered a b c hc hcb hba

private theorem reciprocal_lower (t : ℝ) (ht : 0 ≤ t) :
    1 - t / 2 ≤ 1 / (1 + t^2) := by
  apply (le_div_iff₀ (by positivity : 0 < 1 + t^2)).mpr
  nlinarith only [mul_nonneg ht (sq_nonneg (t-1))]

theorem pulse38_full_source (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : 1 / (1 + a^2) + 1 / (1 + b^2) + 1 / (1 + c^2) = 3 / 2) :
    3 ≤ a*b + b*c + c*a := by
  let p := a+b+c
  let q := a*b+b*c+c*a
  let r := a*b*c
  have hp : 3 ≤ p := by
    dsimp [p]
    linarith [reciprocal_lower a ha, reciprocal_lower b hb, reciprocal_lower c hc]
  have hp0 : 0 < p := by linarith
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hrelation : p^2 + 2*p*r - 3*r^2 = q^2 + 2*q - 3 := by
    have heq := h
    field_simp [ne_of_gt (show 0 < 1+a^2 by positivity),
      ne_of_gt (show 0 < 1+b^2 by positivity),
      ne_of_gt (show 0 < 1+c^2 by positivity)] at heq
    dsimp [p,q,r]
    nlinarith only [heq]
  by_contra hn
  have hq3 : q < 3 := lt_of_not_ge hn
  have hpq : 3*r*p ≤ q^2 := by
    dsimp [p,q,r]
    nlinarith only [sq_nonneg (a*b-b*c), sq_nonneg (b*c-c*a), sq_nonneg (c*a-a*b)]
  have hprod : 0 ≤ r*(p-3) := mul_nonneg hr0 (sub_nonneg.mpr hp)
  have hr1 : r < 1 := by
    have hh : 0 < (3-q)*(3+q) := mul_pos (sub_pos.mpr hq3) (by linarith)
    nlinarith only [hpq,hprod,hh]
  have hschur : 0 ≤ p^3+9*r-4*p*q := by
    dsimp [p,q,r]
    nlinarith only [schur_three a b c ha hb hc]
  have hfactor : 0 ≤ 2*p^2-3*p*r-9 := by
    have hpos : 0 ≤ (p-3)*(2*p+3)+3*p*(1-r) := by
      exact add_nonneg (mul_nonneg (sub_nonneg.mpr hp) (by linarith))
        (mul_nonneg (by positivity) (by linarith))
    nlinarith only [hpos]
  have hmain : 0 ≤ p*(p^2+2*p*r-3*r^2-4*q) := by
    nlinarith only [hschur, mul_nonneg hr0 hfactor]
  have hbound : 0 ≤ p^2+2*p*r-3*r^2-4*q :=
    (mul_nonneg_iff_of_pos_left hp0).mp hmain
  have hnegative : (q-3)*(q+1) < 0 :=
    mul_neg_of_neg_of_pos (by linarith) (by linarith)
  nlinarith only [hrelation,hbound,hnegative]

theorem solution (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0)
    (habc : a*b*c = 1)
    (h : 1 / (1 + a^2) + 1 / (1 + b^2) + 1 / (1 + c^2) = 3 / 2) :
    a*b+b*c+c*a ≥ 3 := by
  exact pulse38_full_source a b c ha hb hc h
