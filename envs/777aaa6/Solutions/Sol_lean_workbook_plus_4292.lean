-- Prove2me | solution 1 for lean_workbook_plus_4292
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:29:23.848593+00:00
-- url     : https://prove2.me/submissions/260782d5-f238-441b-a88a-154ac0370456

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (1 / a + 1 / b + 1 / c) ≥ (2 / (a + b) + 2 / (b + c) + 2 / (c + a)) ∧ (2 / (a + b) + 2 / (b + c) + 2 / (c + a)) ≥ 9 / (a + b + c) := by
  have pairBound (u v : ℝ) (hu : 0 < u) (hv : 0 < v) : 4/(u+v) ≤ 1/u+1/v := by
    have hs : 0 < u+v := by linarith
    have he : 1/u+1/v-4/(u+v) = (u-v)^2/(u*v*(u+v)) := by
      field_simp [ne_of_gt hu,ne_of_gt hv,ne_of_gt hs]
      <;> ring
    have hn : 0 ≤ (u-v)^2/(u*v*(u+v)) := by positivity
    linarith
  have hab : 0 < a+b := by linarith
  have hbc : 0 < b+c := by linarith
  have hca : 0 < c+a := by linarith
  have hs : 0 < a+b+c := by linarith
  have upper : 2/(a+b)+2/(b+c)+2/(c+a) ≤ 1/a+1/b+1/c := by
    have hp1 := pairBound a b ha hb
    have hp2 := pairBound b c hb hc
    have hp3 := pairBound c a hc ha
    simp only [div_eq_mul_inv] at hp1 hp2 hp3 ⊢
    linarith only [hp1,hp2,hp3]
  have h1 : 0 ≤ (a-c)^2/((a+b)*(b+c)) := by positivity
  have h2 : 0 ≤ (b-a)^2/((b+c)*(c+a)) := by positivity
  have h3 : 0 ≤ (c-b)^2/((c+a)*(a+b)) := by positivity
  have he : 2/(a+b)+2/(b+c)+2/(c+a)-9/(a+b+c) =
      ((a-c)^2/((a+b)*(b+c))+(b-a)^2/((b+c)*(c+a))+(c-b)^2/((c+a)*(a+b)))/(a+b+c) := by
    field_simp [ne_of_gt hab,ne_of_gt hbc,ne_of_gt hca,ne_of_gt hs]
    <;> ring
  have hn : 0 ≤ ((a-c)^2/((a+b)*(b+c))+(b-a)^2/((b+c)*(c+a))+(c-b)^2/((c+a)*(a+b)))/(a+b+c) :=
    div_nonneg (by linarith) hs.le
  have lower : 9/(a+b+c) ≤ 2/(a+b)+2/(b+c)+2/(c+a) := by linarith
  simp only [div_eq_mul_inv] at upper lower ⊢
  constructor <;> linarith only [upper,lower]
