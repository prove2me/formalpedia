-- Prove2me | solution 1 for lean_workbook_plus_73699
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T09:14:03.043661+00:00
-- url     : https://prove2.me/submissions/f4a754a0-92a2-4eb0-896b-f6611b9fe719

import Mathlib

namespace VascNonnegativeSharpBound

theorem schur_ordered (a b c : ℝ) (hc : 0 ≤ c) (hab : b ≤ a) (hbc : c ≤ b) :
    a ^ 2 * (b + c - a) + b ^ 2 * (a + c - b) + c ^ 2 * (a + b - c) ≤
      3 * a * b * c := by
  have h1 := mul_nonneg (sq_nonneg (a - b)) (show 0 ≤ a + b - c by linarith)
  have h2 := mul_nonneg hc
    (mul_nonneg (sub_nonneg.mpr (hbc.trans hab)) (sub_nonneg.mpr hbc))
  nlinarith

theorem schur_nonnegative (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    4 * (a + b + c) * (a * b + b * c + c * a) ≤
      (a + b + c) ^ 3 + 9 * a * b * c := by
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
      · nlinarith [schur_ordered a b c hc hba hcb]

theorem sum_square_facts (a b c : ℝ) (hq : a * b + b * c + c * a = 3) :
    (a + b + c) ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 + 6 ∧
      3 ≤ a ^ 2 + b ^ 2 + c ^ 2 := by
  constructor
  · nlinarith
  · nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]

theorem sum_at_least_three (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hq : a * b + b * c + c * a = 3) : 3 ≤ a + b + c := by
  have hf := sum_square_facts a b c hq
  apply (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 3) (by positivity : 0 ≤ a + b + c)).mp
  nlinarith [hf.1, hf.2]

theorem nonnegative_bound (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hq : a * b + b * c + c * a = 3) :
    6 ≤ a ^ 2 + b ^ 2 + c ^ 2 + 3 * a * b * c := by
  have hs := sum_at_least_three a b c ha hb hc hq
  have hf := (sum_square_facts a b c hq).1
  have hr := mul_nonneg (mul_nonneg ha hb) hc
  by_cases ht : 12 ≤ (a + b + c) ^ 2
  · nlinarith
  · have hp := mul_nonneg (sub_nonneg.mpr hs)
      (sub_nonneg.mpr (le_of_lt (lt_of_not_ge ht)))
    have hsch := schur_nonnegative a b c ha hb hc
    rw [hq] at hsch
    nlinarith

theorem ones_of_sum_three (a b c : ℝ) (hq : a * b + b * c + c * a = 3)
    (hs : a + b + c = 3) : a = 1 ∧ b = 1 ∧ c = 1 := by
  have hf := (sum_square_facts a b c hq).1
  have hS : a ^ 2 + b ^ 2 + c ^ 2 = 3 := by nlinarith
  have ha : a = 1 := by nlinarith [sq_nonneg (b - 1), sq_nonneg (c - 1)]
  have hb : b = 1 := by nlinarith [sq_nonneg (a - 1), sq_nonneg (c - 1)]
  exact ⟨ha, hb, by linarith⟩

theorem positive_product_equality (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hq : a * b + b * c + c * a = 3) (hr : 0 < a * b * c)
    (he : a ^ 2 + b ^ 2 + c ^ 2 + 3 * a * b * c = 6) :
    a = 1 ∧ b = 1 ∧ c = 1 := by
  have hs := sum_at_least_three a b c ha hb hc hq
  have hf := (sum_square_facts a b c hq).1
  have ht : (a + b + c) ^ 2 < 12 := by nlinarith
  have hp := mul_nonneg (sub_nonneg.mpr hs) (sub_nonneg.mpr ht.le)
  have hsch := schur_nonnegative a b c ha hb hc
  rw [hq] at hsch
  have hz : (a + b + c - 3) * (12 - (a + b + c) ^ 2) = 0 := by nlinarith
  have hs0 := (mul_eq_zero.mp hz).resolve_right (ne_of_gt (sub_pos.mpr ht))
  exact ones_of_sum_three a b c hq (by linarith)

theorem boundary_pair (b c : ℝ) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hp : b * c = 3) (hs : b ^ 2 + c ^ 2 = 6) :
    b = Real.sqrt 3 ∧ c = Real.sqrt 3 := by
  have hbc : b = c := by nlinarith [sq_nonneg (b - c)]
  have hr := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hb' : b = Real.sqrt 3 := by
    apply (sq_eq_sq₀ hb (Real.sqrt_nonneg 3)).mp
    nlinarith
  exact ⟨hb', by linarith⟩

theorem equality_iff (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hq : a * b + b * c + c * a = 3) :
    a ^ 2 + b ^ 2 + c ^ 2 + 3 * a * b * c = 6 ↔
      (a = 1 ∧ b = 1 ∧ c = 1) ∨
      (a = 0 ∧ b = Real.sqrt 3 ∧ c = Real.sqrt 3) ∨
      (a = Real.sqrt 3 ∧ b = 0 ∧ c = Real.sqrt 3) ∨
      (a = Real.sqrt 3 ∧ b = Real.sqrt 3 ∧ c = 0) := by
  constructor
  · intro he
    by_cases hr : a * b * c = 0
    · rcases mul_eq_zero.mp hr with hab | hc0
      · rcases mul_eq_zero.mp hab with ha0 | hb0
        · rw [ha0] at hq he
          have hp : b * c = 3 := by nlinarith
          have hS : b ^ 2 + c ^ 2 = 6 := by nlinarith
          obtain ⟨hb', hc'⟩ := boundary_pair b c hb hc hp hS
          exact Or.inr (Or.inl ⟨ha0, hb', hc'⟩)
        · rw [hb0] at hq he
          have hp : a * c = 3 := by nlinarith
          have hS : a ^ 2 + c ^ 2 = 6 := by nlinarith
          obtain ⟨ha', hc'⟩ := boundary_pair a c ha hc hp hS
          exact Or.inr (Or.inr (Or.inl ⟨ha', hb0, hc'⟩))
      · rw [hc0] at hq he
        have hp : a * b = 3 := by nlinarith
        have hS : a ^ 2 + b ^ 2 = 6 := by nlinarith
        obtain ⟨ha', hb'⟩ := boundary_pair a b ha hb hp hS
        exact Or.inr (Or.inr (Or.inr ⟨ha', hb', hc0⟩))
    · have hp : 0 < a * b * c :=
        lt_of_le_of_ne (mul_nonneg (mul_nonneg ha hb) hc) (Ne.symm hr)
      exact Or.inl (positive_product_equality a b c ha hb hc hq hp he)
  · have hr := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
    rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩)
    all_goals nlinarith

theorem source_second_bound (a b c : ℝ) (hq : a * b + b * c + c * a = 3) :
    a + b + c ≤ a ^ 2 + b ^ 2 + c ^ 2 := by
  have hf := sum_square_facts a b c hq
  by_cases hs : a + b + c ≤ 3
  · linarith [hf.2]
  · have hp := mul_nonneg
      (show 0 ≤ a + b + c - 3 by linarith)
      (show 0 ≤ a + b + c + 2 by linarith)
    nlinarith [hf.1]

theorem source_second_equality (a b c : ℝ) (hq : a * b + b * c + c * a = 3) :
    a ^ 2 + b ^ 2 + c ^ 2 = a + b + c ↔ a = 1 ∧ b = 1 ∧ c = 1 := by
  constructor
  · intro he
    have hf := sum_square_facts a b c hq
    have hs : a + b + c = 3 := by nlinarith [hf.1, hf.2]
    exact ones_of_sum_three a b c hq hs
  · rintro ⟨rfl, rfl, rfl⟩
    norm_num

end VascNonnegativeSharpBound

theorem solution : ¬ (∀ a b c : ℝ, a * b + b * c + c * a = 3 →
    a ^ 2 + b ^ 2 + c ^ 2 + 3 * a * b * c ≥ 6) := by
  intro h
  have hf := h (-1) (-1) (-1) (by ring)
  have hz : (-1 : ℝ) ^ 2 + (-1) ^ 2 + (-1) ^ 2 + 3 * (-1) * (-1) * (-1) = 0 := by ring
  rw [hz] at hf
  norm_num at hf

#print axioms VascNonnegativeSharpBound.schur_ordered
#print axioms VascNonnegativeSharpBound.schur_nonnegative
#print axioms VascNonnegativeSharpBound.sum_square_facts
#print axioms VascNonnegativeSharpBound.sum_at_least_three
#print axioms VascNonnegativeSharpBound.nonnegative_bound
#print axioms VascNonnegativeSharpBound.ones_of_sum_three
#print axioms VascNonnegativeSharpBound.positive_product_equality
#print axioms VascNonnegativeSharpBound.boundary_pair
#print axioms VascNonnegativeSharpBound.equality_iff
#print axioms VascNonnegativeSharpBound.source_second_bound
#print axioms VascNonnegativeSharpBound.source_second_equality
#print axioms solution
