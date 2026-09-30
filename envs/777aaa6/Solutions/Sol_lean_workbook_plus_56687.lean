-- Prove2me | solution 1 for lean_workbook_plus_56687
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:40:46.170285+00:00
-- url     : https://prove2.me/submissions/a1651915-fc0e-483e-ade5-ee7033d097b0

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

theorem constraint_certificate (a b c : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c)
    (h : (a + b) / c + (b + c) / (2 * a) + (c + a) / b = 13 / 2) :
    0 < 17 * a - (b + c) ∧
      (b + c) * (a - (b + c)) * (8 * a - (b + c)) +
        (17 * a - (b + c)) * (b - c) ^ 2 = 0 := by
  have he : (17 * a - (b + c)) * (b * c) =
      2 * a * (b + c) * (a + b + c) := by
    field_simp [ne_of_gt ha, ne_of_gt hb, ne_of_gt hc] at h
    nlinarith [h]
  have hp : 0 < (17 * a - (b + c)) * (b * c) := by
    rw [he]
    positivity
  refine ⟨(mul_pos_iff_of_pos_right (mul_pos hb hc)).mp hp, ?_⟩
  nlinarith [he]

theorem sharp_two_sided_bound (a b c : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c)
    (h : (a + b) / c + (b + c) / (2 * a) + (c + a) / b = 13 / 2) :
    a ≤ b + c ∧ b + c ≤ 8 * a := by
  obtain ⟨ht, he⟩ := constraint_certificate a b c ha hb hc h
  have hn := mul_nonneg (le_of_lt ht) (sq_nonneg (b - c))
  have hp : (a - (b + c)) * (8 * a - (b + c)) ≤ 0 := by
    apply (mul_le_mul_iff_right₀ (add_pos hb hc)).mp
    nlinarith [he]
  constructor
  · by_contra hh
    have h1 : 0 < a - (b + c) := by linarith
    have h2 : 0 < 8 * a - (b + c) := by linarith
    have hpos := mul_pos h1 h2
    linarith
  · by_contra hh
    have h1 : a - (b + c) < 0 := by linarith
    have h2 : 8 * a - (b + c) < 0 := by linarith
    have hpos := mul_pos_of_neg_of_neg h1 h2
    linarith

theorem endpoints_iff_equal (a b c : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c)
    (h : (a + b) / c + (b + c) / (2 * a) + (c + a) / b = 13 / 2) :
    (a = b + c ∨ b + c = 8 * a) ↔ b = c := by
  obtain ⟨ht, he⟩ := constraint_certificate a b c ha hb hc h
  constructor
  · intro hend
    have hp : (17 * a - (b + c)) * (b - c) ^ 2 = 0 := by
      rcases hend with h1 | h2
      · have hz : a - (b + c) = 0 := sub_eq_zero.mpr h1
        simpa only [hz, mul_zero, zero_mul, zero_add] using he
      · have hz : 8 * a - (b + c) = 0 := sub_eq_zero.mpr h2.symm
        simpa only [hz, mul_zero, zero_mul, zero_add] using he
    have hs := (mul_eq_zero.mp hp).resolve_left (ne_of_gt ht)
    have hz := sq_eq_zero_iff.mp hs
    linarith
  · intro hbc
    have hp : (b + c) * ((a - (b + c)) * (8 * a - (b + c))) = 0 := by
      rw [hbc] at he ⊢
      nlinarith [he]
    have hq := (mul_eq_zero.mp hp).resolve_left (ne_of_gt (add_pos hb hc))
    rcases mul_eq_zero.mp hq with h1 | h2
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)

theorem endpoint_families (t : ℝ) (ht : 0 < t) :
    (2 * t + t) / t + (t + t) / (2 * (2 * t)) + (t + 2 * t) / t = 13 / 2 ∧
    (t + 4 * t) / (4 * t) + (4 * t + 4 * t) / (2 * t) +
      (4 * t + t) / (4 * t) = 13 / 2 := by
  constructor <;> field_simp [ne_of_gt ht] <;> ring

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a + b) / c + (b + c) / (2 * a) + (c + a) / b = 13 / 2 → a ≤ b + c := by
  intro h
  exact (sharp_two_sided_bound a b c ha hb hc h).1
