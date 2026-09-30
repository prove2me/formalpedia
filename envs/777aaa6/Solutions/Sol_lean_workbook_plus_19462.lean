-- Prove2me | solution 1 for lean_workbook_plus_19462
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T16:47:47.917159+00:00
-- url     : https://prove2.me/submissions/1fc66467-841a-4a7e-80f2-9a941790a0d5

import Mathlib.Analysis.Complex.Basic

/-- Schur's inequality of degree one for nonnegative reals. -/
lemma schur_deg_one_aux (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hab : b ≤ a) (hbc : c ≤ b) :
    0 ≤ a * (a - b) * (a - c) + b * (b - a) * (b - c) + c * (c - a) * (c - b) := by
  have h1 : 0 ≤ (a - b) ^ 2 * (a + b - c) := by
    apply mul_nonneg (sq_nonneg _); linarith
  have h2 : 0 ≤ c * (a - c) * (b - c) := by
    apply mul_nonneg (mul_nonneg hc (by linarith)) (by linarith)
  nlinarith [h1, h2]

lemma schur_deg_one (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    0 ≤ a * (a - b) * (a - c) + b * (b - a) * (b - c) + c * (c - a) * (c - b) := by
  rcases le_total a b with hab | hab <;> rcases le_total b c with hbc | hbc <;>
    rcases le_total a c with hac | hac
  · have := schur_deg_one_aux c b a hc hb ha hbc hab; linarith
  · have := schur_deg_one_aux c b a hc hb ha hbc hab; linarith
  · have := schur_deg_one_aux b c a hb hc ha hbc hac; linarith
  · have := schur_deg_one_aux b a c hb ha hc hab hac; linarith
  · have := schur_deg_one_aux c a b hc ha hb hac hab; linarith
  · have := schur_deg_one_aux a c b ha hc hb hac hbc; linarith
  · have := schur_deg_one_aux a b c ha hb hc hab hbc; linarith
  · have := schur_deg_one_aux a b c ha hb hc hab hbc; linarith

theorem solution : ∀ a b c : ℝ, a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 → (a^2 + a * b + b^2) * (b^2 + b * c + c^2) * (c^2 + c * a + a^2) ≥ 1 / 3 * (a * b + b * c + c * a)^2 * (2 * a^2 + 2 * b^2 + 2 * c^2 + a * b + b * c + c * a) := by
  rintro a b c ⟨ha, hb, hc⟩
  have hs := schur_deg_one a b c ha hb hc
  have habc : 0 ≤ a * b * c := mul_nonneg (mul_nonneg ha hb) hc
  have hsum : 0 ≤ a * b + b * c + c * a := by positivity
  have h1 := mul_nonneg habc hs
  have h2 := mul_nonneg hsum (add_nonneg (add_nonneg (sq_nonneg (a * b - b * c)) (sq_nonneg (b * c - c * a))) (sq_nonneg (c * a - a * b)))
  nlinarith [sq_nonneg (a ^ 2 * (b - c)), sq_nonneg (b ^ 2 * (c - a)), sq_nonneg (c ^ 2 * (a - b)), h1, h2]
