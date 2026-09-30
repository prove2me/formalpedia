-- Prove2me | solution 1 for lean_workbook_plus_72240
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T21:38:01.241648+00:00
-- url     : https://prove2.me/submissions/67393f4e-5bdd-48db-99cb-134169ce6304

import Mathlib

set_option autoImplicit false

noncomputable section

namespace ReciprocalLinearSharpMinimum

def energy (a b c : ℝ) : ℝ := (a + c) ^ 2 / a + (a + c) ^ 2 / b + 7 * a + 4 * b

def coefficient : ℝ := 6 + 4 * Real.sqrt 3

theorem coefficient_gt_ten : 10 < coefficient := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hp := Real.sqrt_nonneg (3 : ℝ)
  unfold coefficient
  nlinarith

theorem gap_identity (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) :
    energy a b c - coefficient * c =
      (2 * Real.sqrt 3 * a - c) ^ 2 / a + (2 * b - a - c) ^ 2 / b := by
  have hi : (2 * Real.sqrt 3 * a - c) ^ 2 =
      12 * a ^ 2 - 4 * Real.sqrt 3 * a * c + c ^ 2 := by
    calc
      _ = 4 * a ^ 2 * Real.sqrt 3 ^ 2 - 4 * Real.sqrt 3 * a * c + c ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]; ring
  unfold energy coefficient
  field_simp
  linear_combination -b * hi

theorem sharp_bound (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) :
    coefficient * c ≤ energy a b c := by
  have hi := gap_identity a b c ha hb
  have h1 := div_nonneg (sq_nonneg (2 * Real.sqrt 3 * a - c)) ha.le
  have h2 := div_nonneg (sq_nonneg (2 * b - a - c)) hb.le
  linarith only [hi, h1, h2]

theorem equality_iff (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) :
    energy a b c = coefficient * c ↔ 2 * Real.sqrt 3 * a = c ∧ 2 * b = a + c := by
  have hi := gap_identity a b c ha hb
  have h1 := div_nonneg (sq_nonneg (2 * Real.sqrt 3 * a - c)) ha.le
  have h2 := div_nonneg (sq_nonneg (2 * b - a - c)) hb.le
  constructor
  · intro he
    have hz1 : (2 * Real.sqrt 3 * a - c) ^ 2 / a = 0 := by linarith only [hi, he, h1, h2]
    have hz2 : (2 * b - a - c) ^ 2 / b = 0 := by linarith only [hi, he, h1, h2]
    have hs1 := sq_eq_zero_iff.mp ((div_eq_zero_iff.mp hz1).resolve_right ha.ne')
    have hs2 := sq_eq_zero_iff.mp ((div_eq_zero_iff.mp hz2).resolve_right hb.ne')
    exact ⟨sub_eq_zero.mp hs1, by linarith only [hs2]⟩
  · rintro ⟨he1, he2⟩
    have hz1 : 2 * Real.sqrt 3 * a - c = 0 := by linarith only [he1]
    have hz2 : 2 * b - a - c = 0 := by linarith only [he2]
    rw [hz1, hz2] at hi
    exact sub_eq_zero.mp (by simpa using hi)

theorem minimizer (c : ℝ) (hc : 0 < c) :
    let a := c / (2 * Real.sqrt 3)
    let b := (a + c) / 2
    0 < a ∧ 0 < b ∧ a < c ∧ energy a b c = coefficient * c := by
  dsimp
  have hr : (0 : ℝ) < Real.sqrt 3 := by positivity
  have ha : 0 < c / (2 * Real.sqrt 3) := div_pos hc (by positivity)
  have hb : 0 < (c / (2 * Real.sqrt 3) + c) / 2 := by positivity
  have he : 2 * Real.sqrt 3 * (c / (2 * Real.sqrt 3)) = c := by
    field_simp
  refine ⟨ha, hb, ?_, (equality_iff _ _ _ ha hb).mpr ⟨he, by ring⟩⟩
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hr1 : 1 < 2 * Real.sqrt 3 := by nlinarith
  have hlt := mul_lt_mul_of_pos_right hr1 ha
  nlinarith only [hlt, he]

theorem unique_minimizer (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) :
    energy a b c = coefficient * c ↔
      a = c / (2 * Real.sqrt 3) ∧ b = (c / (2 * Real.sqrt 3) + c) / 2 := by
  have hr : (0 : ℝ) < Real.sqrt 3 := by positivity
  rw [equality_iff a b c ha hb]
  constructor
  · rintro ⟨he1, he2⟩
    have hea : a = c / (2 * Real.sqrt 3) := (eq_div_iff (by positivity)).mpr (by linarith)
    exact ⟨hea, by rw [← hea]; linarith only [he2]⟩
  · rintro ⟨rfl, rfl⟩
    constructor
    · field_simp
    · ring

theorem normalized_minimum (c : ℝ) (hc : 0 < c) :
    IsLeast {v : ℝ | ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ energy a b c = v} (coefficient * c) := by
  constructor
  · have hm := minimizer c hc
    exact ⟨_, _, hm.1, hm.2.1, hm.2.2.2⟩
  · rintro v ⟨a, b, ha, hb, rfl⟩
    exact sharp_bound a b c ha hb

theorem sharp_coefficient (k : ℝ) :
    (∀ a b c : ℝ, 0 < a → 0 < b → 0 < c → k * c ≤ energy a b c) ↔ k ≤ coefficient := by
  constructor
  · intro h
    have hm := minimizer 1 (by norm_num)
    have he := h _ _ 1 hm.1 hm.2.1 (by norm_num)
    rw [hm.2.2.2] at he
    simpa only [mul_one] using he
  · intro hk a b c ha hb hc
    exact (mul_le_mul_of_nonneg_right hk hc.le).trans (sharp_bound a b c ha hb)

theorem strict_ten_bound (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    10 * c < energy a b c :=
  (mul_lt_mul_of_pos_right coefficient_gt_ten hc).trans_le (sharp_bound a b c ha hb)

theorem necessary_coefficient (a b c K k : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : k * c = 7 * a + 4 * b + K)
    (h2 : K = (a + c) ^ 2 / a + (c + a) ^ 2 / b) : coefficient ≤ k := by
  have he : energy a b c = k * c := by
    unfold energy
    rw [add_comm c a] at h2
    linarith only [h1, h2]
  have hbnd := sharp_bound a b c ha hb
  rw [he] at hbnd
  exact (mul_le_mul_iff_left₀ hc).mp hbnd

theorem source_constraints_impossible (a b c K : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : 10 * c = 7 * a + 4 * b + K)
    (h2 : K = (a + c) ^ 2 / a + (c + a) ^ 2 / b) : False := by
  have hn := necessary_coefficient a b c K 10 ha hb hc h1 h2
  exact (not_le_of_gt coefficient_gt_ten) hn

theorem source_no_solution :
    ¬ ∃ a b c : ℝ, 0 < a ∧ 0 < b ∧ 0 < c ∧ c > a ∧
      10 * c = 7 * a + 4 * b + 2024 ∧
      2024 = (a + c) ^ 2 / a + (c + a) ^ 2 / b := by
  rintro ⟨a, b, c, ha, hb, hc, _, h1, h2⟩
  exact source_constraints_impossible a b c 2024 ha hb hc h1 h2

end ReciprocalLinearSharpMinimum

theorem solution (a b c : ℝ) (h₁ : a > 0 ∧ b > 0 ∧ c > 0) (_h₂ : c > a)
    (h₃ : 10 * c = 7 * a + 4 * b + 2024)
    (h₄ : 2024 = (a + c) ^ 2 / a + (c + a) ^ 2 / b) : a + b + c = 10 := by
  exact (ReciprocalLinearSharpMinimum.source_constraints_impossible a b c 2024
    h₁.1 h₁.2.1 h₁.2.2 h₃ h₄).elim

#print axioms ReciprocalLinearSharpMinimum.energy
#print axioms ReciprocalLinearSharpMinimum.coefficient
#print axioms ReciprocalLinearSharpMinimum.coefficient_gt_ten
#print axioms ReciprocalLinearSharpMinimum.gap_identity
#print axioms ReciprocalLinearSharpMinimum.sharp_bound
#print axioms ReciprocalLinearSharpMinimum.equality_iff
#print axioms ReciprocalLinearSharpMinimum.minimizer
#print axioms ReciprocalLinearSharpMinimum.unique_minimizer
#print axioms ReciprocalLinearSharpMinimum.normalized_minimum
#print axioms ReciprocalLinearSharpMinimum.sharp_coefficient
#print axioms ReciprocalLinearSharpMinimum.strict_ten_bound
#print axioms ReciprocalLinearSharpMinimum.necessary_coefficient
#print axioms ReciprocalLinearSharpMinimum.source_constraints_impossible
#print axioms ReciprocalLinearSharpMinimum.source_no_solution
#print axioms solution
