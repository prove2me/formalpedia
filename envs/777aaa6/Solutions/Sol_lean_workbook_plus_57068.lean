-- Prove2me | solution 1 for lean_workbook_plus_57068
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:33:00.923352+00:00
-- url     : https://prove2.me/submissions/a6b05cf9-9b42-4cf5-ad04-eeb93772d16d

import Mathlib

namespace WeightedBilinearSharpBound

theorem pair_product_bound (a b c : ℝ) :
    3 * ((a * b) ^ 2 + (b * c) ^ 2 + (c * a) ^ 2) ≤ (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 := by
  nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (b ^ 2 - c ^ 2),
    sq_nonneg (c ^ 2 - a ^ 2)]

theorem cauchy_three (x y z a b c : ℝ) :
    (x * a + y * b + z * c) ^ 2 ≤
      (x ^ 2 + y ^ 2 + z ^ 2) * (a ^ 2 + b ^ 2 + c ^ 2) := by
  nlinarith [sq_nonneg (x * b - y * a), sq_nonneg (y * c - z * b),
    sq_nonneg (z * a - x * c)]

theorem sum_square_bound (x y z : ℝ) :
    (x + y + z) ^ 2 ≤ 3 * (x ^ 2 + y ^ 2 + z ^ 2) := by
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]

theorem sum_square_equality (x y z : ℝ) :
    (x + y + z) ^ 2 = 3 * (x ^ 2 + y ^ 2 + z ^ 2) ↔ x = y ∧ y = z := by
  constructor
  · intro h
    constructor <;> nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
  · rintro ⟨rfl, rfl⟩
    ring

theorem bilinear_square_bound (x y z a b c : ℝ) :
    3 * (x * a * b + y * b * c + z * c * a) ^ 2 ≤
      (x ^ 2 + y ^ 2 + z ^ 2) * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 := by
  have h1 := cauchy_three x y z (a * b) (b * c) (c * a)
  have h2 := pair_product_bound a b c
  calc
    3 * (x * a * b + y * b * c + z * c * a) ^ 2 ≤
        3 * ((x ^ 2 + y ^ 2 + z ^ 2) * ((a * b) ^ 2 + (b * c) ^ 2 + (c * a) ^ 2)) := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 3)
    _ = (x ^ 2 + y ^ 2 + z ^ 2) *
        (3 * ((a * b) ^ 2 + (b * c) ^ 2 + (c * a) ^ 2)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h2 (by positivity)

theorem absolute_bound (x y z a b c : ℝ) :
    |(x + y + z) * (x * a * b + y * b * c + z * c * a)| ≤
      (x ^ 2 + y ^ 2 + z ^ 2) * (a ^ 2 + b ^ 2 + c ^ 2) := by
  let A := x ^ 2 + y ^ 2 + z ^ 2
  let B := a ^ 2 + b ^ 2 + c ^ 2
  let S := x + y + z
  let T := x * a * b + y * b * c + z * c * a
  have hs : S ^ 2 ≤ 3 * A := sum_square_bound x y z
  have ht : 3 * T ^ 2 ≤ A * B ^ 2 := bilinear_square_bound x y z a b c
  have ha : 0 ≤ A := by dsimp [A]; positivity
  have hb : 0 ≤ B := by dsimp [B]; positivity
  have hsq : (S * T) ^ 2 ≤ (A * B) ^ 2 := by
    have hh : 3 * (S * T) ^ 2 ≤ 3 * (A * B) ^ 2 := calc
      3 * (S * T) ^ 2 = S ^ 2 * (3 * T ^ 2) := by ring
      _ ≤ S ^ 2 * (A * B ^ 2) := mul_le_mul_of_nonneg_left ht (sq_nonneg S)
      _ ≤ (3 * A) * (A * B ^ 2) := mul_le_mul_of_nonneg_right hs (by positivity)
      _ = 3 * (A * B) ^ 2 := by ring
    linarith
  exact (sq_le_sq₀ (abs_nonneg _) (mul_nonneg ha hb)).mp (by simpa only [sq_abs] using hsq)

theorem source_bound (x y z a b c : ℝ) :
    (x + y + z) * (x * a * b + y * b * c + z * c * a) ≤
      (x ^ 2 + y ^ 2 + z ^ 2) * (a ^ 2 + b ^ 2 + c ^ 2) :=
  (le_abs_self _).trans (absolute_bound x y z a b c)

theorem equality_iff (x y z a b c : ℝ) :
    (x + y + z) * (x * a * b + y * b * c + z * c * a) =
      (x ^ 2 + y ^ 2 + z ^ 2) * (a ^ 2 + b ^ 2 + c ^ 2) ↔
    (x = 0 ∧ y = 0 ∧ z = 0) ∨ (a = 0 ∧ b = 0 ∧ c = 0) ∨
      (x = y ∧ y = z ∧ a = b ∧ b = c) := by
  constructor
  · intro he
    by_cases hA : x ^ 2 + y ^ 2 + z ^ 2 = 0
    · exact Or.inl ⟨by nlinarith [sq_nonneg y, sq_nonneg z],
        by nlinarith [sq_nonneg x, sq_nonneg z], by nlinarith [sq_nonneg x, sq_nonneg y]⟩
    by_cases hB : a ^ 2 + b ^ 2 + c ^ 2 = 0
    · exact Or.inr (Or.inl ⟨by nlinarith [sq_nonneg b, sq_nonneg c],
        by nlinarith [sq_nonneg a, sq_nonneg c], by nlinarith [sq_nonneg a, sq_nonneg b]⟩)
    have hAp : 0 < x ^ 2 + y ^ 2 + z ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm hA)
    have hBp : 0 < a ^ 2 + b ^ 2 + c ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm hB)
    let A := x ^ 2 + y ^ 2 + z ^ 2
    let B := a ^ 2 + b ^ 2 + c ^ 2
    let S := x + y + z
    let T := x * a * b + y * b * c + z * c * a
    have he' : S * T = A * B := he
    have ht : 3 * T ^ 2 ≤ A * B ^ 2 := bilinear_square_bound x y z a b c
    have hfactor : 0 < A * B ^ 2 := mul_pos hAp (sq_pos_of_pos hBp)
    have hsge : 3 * A ≤ S ^ 2 := by
      apply (mul_le_mul_iff_right₀ hfactor).mp
      calc
        (A * B ^ 2) * (3 * A) = 3 * (S * T) ^ 2 := by rw [he']; ring
        _ = S ^ 2 * (3 * T ^ 2) := by ring
        _ ≤ S ^ 2 * (A * B ^ 2) := mul_le_mul_of_nonneg_left ht (sq_nonneg S)
        _ = (A * B ^ 2) * S ^ 2 := by ring
    obtain ⟨hxy, hyz⟩ := (sum_square_equality x y z).mp
      (le_antisymm (sum_square_bound x y z) hsge)
    subst y
    subst z
    have hx : x ≠ 0 := by intro h; subst x; norm_num at hA
    have hs : a ^ 2 + b ^ 2 + c ^ 2 = a * b + b * c + c * a := by
      apply (mul_left_cancel₀ (show 3 * x ^ 2 ≠ 0 by positivity))
      calc
        3 * x ^ 2 * (a ^ 2 + b ^ 2 + c ^ 2) =
            (x + x + x) * (x * a * b + x * b * c + x * c * a) := by nlinarith [he]
        _ = 3 * x ^ 2 * (a * b + b * c + c * a) := by ring
    exact Or.inr (Or.inr ⟨rfl, rfl,
      by nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)],
      by nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]⟩)
  · rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩) <;> ring

theorem sharp_constant (k : ℝ) :
    (∀ x y z a b c : ℝ, (x + y + z) * (x * a * b + y * b * c + z * c * a) ≤
      k * ((x ^ 2 + y ^ 2 + z ^ 2) * (a ^ 2 + b ^ 2 + c ^ 2))) ↔ 1 ≤ k := by
  constructor
  · intro h
    have hh := h 1 1 1 1 1 1
    norm_num at hh
    exact hh
  · intro hk x y z a b c
    have h := source_bound x y z a b c
    have hnonneg : 0 ≤ (x ^ 2 + y ^ 2 + z ^ 2) * (a ^ 2 + b ^ 2 + c ^ 2) := by positivity
    exact h.trans (le_mul_of_one_le_left hnonneg hk)

end WeightedBilinearSharpBound

theorem solution (x y z a b c : ℝ) :
    (x + y + z) * (x * a * b + y * b * c + z * c * a) ≤
      (x ^ 2 + y ^ 2 + z ^ 2) * (a ^ 2 + b ^ 2 + c ^ 2) :=
  WeightedBilinearSharpBound.source_bound x y z a b c

#print axioms WeightedBilinearSharpBound.pair_product_bound
#print axioms WeightedBilinearSharpBound.cauchy_three
#print axioms WeightedBilinearSharpBound.sum_square_bound
#print axioms WeightedBilinearSharpBound.sum_square_equality
#print axioms WeightedBilinearSharpBound.bilinear_square_bound
#print axioms WeightedBilinearSharpBound.absolute_bound
#print axioms WeightedBilinearSharpBound.source_bound
#print axioms WeightedBilinearSharpBound.equality_iff
#print axioms WeightedBilinearSharpBound.sharp_constant
#print axioms solution
