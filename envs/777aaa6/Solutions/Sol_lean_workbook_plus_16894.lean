-- Prove2me | solution 1 for lean_workbook_plus_16894
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T23:36:20.383944+00:00
-- url     : https://prove2.me/submissions/ed35b0dc-f14c-4fc4-97d5-52a021e2c6e6

import Mathlib

set_option autoImplicit false

noncomputable section

namespace SymmetricCubicThreePoint

def cubic (A B C a b c : ℝ) : ℝ :=
  A * (a ^ 3 + b ^ 3 + c ^ 3) +
  B * (a ^ 2 * (b + c) + b ^ 2 * (a + c) + c ^ 2 * (a + b)) + C * a * b * c

def schur (a b c : ℝ) : ℝ :=
  a ^ 3 + b ^ 3 + c ^ 3 -
    (a ^ 2 * (b + c) + b ^ 2 * (a + c) + c ^ 2 * (a + b)) + 3 * a * b * c

def mixedGap (a b c : ℝ) : ℝ :=
  a * (b - c) ^ 2 + b * (a - c) ^ 2 + c * (a - b) ^ 2

theorem cubic_swap_left (A B C a b c : ℝ) : cubic A B C a b c = cubic A B C b a c := by
  unfold cubic
  ring

theorem cubic_swap_right (A B C a b c : ℝ) : cubic A B C a b c = cubic A B C a c b := by
  unfold cubic
  ring

theorem cubic_homogeneous (A B C t a b c : ℝ) :
    cubic A B C (t * a) (t * b) (t * c) = t ^ 3 * cubic A B C a b c := by
  unfold cubic
  ring

theorem sample_values (A B C : ℝ) :
    cubic A B C 1 0 0 = A ∧ cubic A B C 1 1 0 = 2 * (A + B) ∧
      cubic A B C 1 1 1 = 3 * A + 6 * B + C := by
  unfold cubic
  constructor
  · ring
  constructor <;> ring

theorem decomposition (A B C a b c : ℝ) :
    cubic A B C a b c = A * schur a b c + (A + B) * mixedGap a b c +
      (3 * A + 6 * B + C) * (a * b * c) := by
  unfold cubic schur mixedGap
  ring

theorem sample_reconstruction (A B C a b c : ℝ) :
    cubic A B C a b c = cubic A B C 1 0 0 * schur a b c +
      (cubic A B C 1 1 0 / 2) * mixedGap a b c + cubic A B C 1 1 1 * (a * b * c) := by
  unfold cubic schur mixedGap
  ring

theorem coefficients_unique {A B C D E F : ℝ}
    (h : ∀ a b c : ℝ, cubic A B C a b c = cubic D E F a b c) :
    A = D ∧ B = E ∧ C = F := by
  have h1 := h 1 0 0
  have h2 := h 1 1 0
  have h3 := h 1 1 1
  rw [(sample_values A B C).1, (sample_values D E F).1] at h1
  rw [(sample_values A B C).2.1, (sample_values D E F).2.1] at h2
  rw [(sample_values A B C).2.2, (sample_values D E F).2.2] at h3
  exact ⟨h1, by linarith only [h1, h2], by linarith only [h1, h2, h3]⟩

-- This weighted-square Schur identity is the disclosed shared ingredient.
theorem schur_weighted_identity (a b c : ℝ) :
    (a + (b + c) / 4) * schur a b c = b * c * (b - c) ^ 2 +
      (c * a * (c - a) ^ 2 + a * b * (a - b) ^ 2) / 4 +
      (2 * a ^ 2 - b ^ 2 - c ^ 2 - a * b + 2 * b * c - c * a) ^ 2 / 4 := by
  unfold schur
  ring

theorem schur_nonnegative {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    0 ≤ schur a b c := by
  by_cases hz : a + b + c = 0
  · have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    have hc0 : c = 0 := by linarith
    simp [ha0, hb0, hc0, schur]
  · have hp : 0 < a + (b + c) / 4 := by
      have hs : 0 < a + b + c := lt_of_le_of_ne (by positivity) (Ne.symm hz)
      linarith
    have hn : 0 ≤ (a + (b + c) / 4) * schur a b c := by
      rw [schur_weighted_identity]
      positivity
    exact nonneg_of_mul_nonneg_right hn hp

theorem mixed_nonnegative {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    0 ≤ mixedGap a b c := by
  unfold mixedGap
  positivity

theorem coefficient_criterion (A B C : ℝ) :
    (∀ a b c : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ c → 0 ≤ cubic A B C a b c) ↔
      0 ≤ A ∧ 0 ≤ A + B ∧ 0 ≤ 3 * A + 6 * B + C := by
  constructor
  · intro h
    have h1 := h 1 0 0 (by norm_num) (by norm_num) (by norm_num)
    have h2 := h 1 1 0 (by norm_num) (by norm_num) (by norm_num)
    have h3 := h 1 1 1 (by norm_num) (by norm_num) (by norm_num)
    rw [(sample_values A B C).1] at h1
    rw [(sample_values A B C).2.1] at h2
    rw [(sample_values A B C).2.2] at h3
    exact ⟨h1, by linarith only [h2], h3⟩
  · rintro ⟨hA, hB, hC⟩ a b c ha hb hc
    rw [decomposition]
    exact add_nonneg
      (add_nonneg (mul_nonneg hA (schur_nonnegative ha hb hc))
        (mul_nonneg hB (mixed_nonnegative ha hb hc)))
      (mul_nonneg hC (mul_nonneg (mul_nonneg ha hb) hc))

theorem three_point_criterion (A B C : ℝ) :
    (0 ≤ cubic A B C 1 1 1 ∧ 0 ≤ cubic A B C 1 1 0 ∧ 0 ≤ cubic A B C 1 0 0) ↔
      (∀ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c → 0 ≤ cubic A B C a b c) := by
  constructor
  · rintro ⟨h3, h2, h1⟩ a b c ⟨ha, hb, hc⟩
    apply (coefficient_criterion A B C).mpr _ a b c ha hb hc
    rw [(sample_values A B C).1] at h1
    rw [(sample_values A B C).2.1] at h2
    rw [(sample_values A B C).2.2] at h3
    exact ⟨h1, by linarith only [h2], h3⟩
  · intro h
    exact ⟨h 1 1 1 (by norm_num), h 1 1 0 (by norm_num), h 1 0 0 (by norm_num)⟩

theorem zero_criterion {A B C a b c : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ A + B) (hC : 0 ≤ 3 * A + 6 * B + C)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    cubic A B C a b c = 0 ↔
      (A = 0 ∨ schur a b c = 0) ∧
      (A + B = 0 ∨ mixedGap a b c = 0) ∧
      (3 * A + 6 * B + C = 0 ∨ a * b * c = 0) := by
  have h1 := mul_nonneg hA (schur_nonnegative ha hb hc)
  have h2 := mul_nonneg hB (mixed_nonnegative ha hb hc)
  have h3 := mul_nonneg hC (mul_nonneg (mul_nonneg ha hb) hc)
  have hid := decomposition A B C a b c
  constructor
  · intro he
    exact ⟨mul_eq_zero.mp (by linarith only [he, hid, h1, h2, h3]),
      mul_eq_zero.mp (by linarith only [he, hid, h1, h2, h3]),
      mul_eq_zero.mp (by linarith only [he, hid, h1, h2, h3])⟩
  · rintro ⟨he1, he2, he3⟩
    rw [hid, mul_eq_zero.mpr he1, mul_eq_zero.mpr he2, mul_eq_zero.mpr he3]
    ring

theorem interior_positive {A B C a b c : ℝ}
    (hA : 0 < A) (hB : 0 < A + B) (hC : 0 < 3 * A + 6 * B + C)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hs : 0 < a + b + c) :
    0 < cubic A B C a b c := by
  have hn := (coefficient_criterion A B C).mpr ⟨hA.le, hB.le, hC.le⟩ a b c ha hb hc
  by_contra! hle
  have hz := (zero_criterion hA.le hB.le hC.le ha hb hc).mp (le_antisymm hle hn)
  have hS := hz.1.resolve_left (ne_of_gt hA)
  have hQ := hz.2.1.resolve_left (ne_of_gt hB)
  have hR := hz.2.2.resolve_left (ne_of_gt hC)
  have he : a ^ 3 + b ^ 3 + c ^ 3 = 0 := by
    unfold schur at hS
    unfold mixedGap at hQ
    nlinarith only [hS, hQ, hR]
  have ha3 : a ^ 3 = 0 := by nlinarith only [he, pow_nonneg ha 3, pow_nonneg hb 3, pow_nonneg hc 3]
  have hb3 : b ^ 3 = 0 := by nlinarith only [he, pow_nonneg ha 3, pow_nonneg hb 3, pow_nonneg hc 3]
  have hc3 : c ^ 3 = 0 := by nlinarith only [he, pow_nonneg ha 3, pow_nonneg hb 3, pow_nonneg hc 3]
  have ha0 : a = 0 := eq_zero_of_pow_eq_zero ha3
  have hb0 : b = 0 := eq_zero_of_pow_eq_zero hb3
  have hc0 : c = 0 := eq_zero_of_pow_eq_zero hc3
  linarith only [hs, ha0, hb0, hc0]

def counterPolynomial : Polynomial ℝ :=
  -((Polynomial.X - 1) * (Polynomial.X - 2) * (Polynomial.X - 3))

def counterexample (a b c : ℝ) : ℝ := counterPolynomial.eval (a + b + c)

theorem counter_degree : counterPolynomial.natDegree = 3 := by
  have he : counterPolynomial = -Polynomial.X ^ 3 + 6 * Polynomial.X ^ 2 -
      11 * Polynomial.X + 6 := by
    unfold counterPolynomial
    ring
  rw [he]
  compute_degree!

theorem counter_formula (a b c : ℝ) :
    counterexample a b c = -((a + b + c - 1) * (a + b + c - 2) * (a + b + c - 3)) := by
  simp [counterexample, counterPolynomial]

theorem counter_symmetry (a b c : ℝ) :
    counterexample a b c = counterexample b a c ∧
      counterexample a b c = counterexample a c b := by
  simp [counterexample, add_comm, add_left_comm]

theorem counter_tests :
    counterexample 1 1 1 = 0 ∧ counterexample 1 1 0 = 0 ∧
      counterexample 1 0 0 = 0 ∧ counterexample 4 0 0 = -6 := by
  simp only [counter_formula]
  norm_num

theorem counter_not_homogeneous :
    ¬ (∀ t a b c : ℝ, counterexample (t * a) (t * b) (t * c) =
      t ^ 3 * counterexample a b c) := by
  intro h
  have he := h 0 0 0 0
  simp only [counter_formula] at he
  norm_num at he
  exact (by norm_num : (6 : ℝ) ≠ 0) he

theorem symmetric_cubic_test_failure :
    ∃ p : Polynomial ℝ, p.natDegree = 3 ∧
      0 ≤ p.eval (1 + 1 + 1) ∧ 0 ≤ p.eval (1 + 1 + 0) ∧ 0 ≤ p.eval (1 + 0 + 0) ∧
      ¬ (∀ a b c : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ c → 0 ≤ p.eval (a + b + c)) := by
  refine ⟨counterPolynomial, counter_degree, ?_, ?_, ?_, ?_⟩
  · change 0 ≤ counterexample 1 1 1
    rw [counter_tests.1]
  · change 0 ≤ counterexample 1 1 0
    rw [counter_tests.2.1]
  · change 0 ≤ counterexample 1 0 0
    rw [counter_tests.2.2.1]
  · intro h
    have he := h 4 0 0 (by norm_num) (by norm_num) (by norm_num)
    change 0 ≤ counterexample 4 0 0 at he
    rw [counter_tests.2.2.2] at he
    norm_num at he

end SymmetricCubicThreePoint

theorem solution (P : ℝ → ℝ → ℝ → ℝ)
    (h : P = fun a b c ↦ a ^ 3 + b ^ 3 + c ^ 3 - 3 * a * b * c) :
    (P 1 1 1 ≥ 0 ∧ P 1 1 0 ≥ 0 ∧ P 1 0 0 ≥ 0) ↔
      (∀ a b c : ℝ, a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 → P a b c ≥ 0) := by
  subst P
  have he : (fun a b c : ℝ => a ^ 3 + b ^ 3 + c ^ 3 - 3 * a * b * c) =
      SymmetricCubicThreePoint.cubic 1 0 (-3) := by
    funext a b c
    unfold SymmetricCubicThreePoint.cubic
    ring
  rw [he]
  exact SymmetricCubicThreePoint.three_point_criterion 1 0 (-3)
