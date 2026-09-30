-- Prove2me | solution 1 for lean_workbook_plus_55368
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:20:12.35127+00:00
-- url     : https://prove2.me/submissions/927fc48d-9078-4959-9a95-090d3a5f7c34

import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

theorem parameter_necessary (M x y z : ℝ)
    (h1 : |x - M| + y ^ 2 - 3 * z = 4)
    (h2 : |y - M| + z ^ 2 - 3 * x = 4)
    (h3 : |z - M| + x ^ 2 - 3 * y = 4) : -5 ≤ M ∧ M ≤ 8 := by
  constructor
  · nlinarith [le_abs_self (x - M), le_abs_self (y - M), le_abs_self (z - M),
      sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1)]
  · nlinarith [neg_le_abs (x - M), neg_le_abs (y - M), neg_le_abs (z - M),
      sq_nonneg (x - 2), sq_nonneg (y - 2), sq_nonneg (z - 2)]

theorem lower_parameter_witness (M : ℝ) (hlo : -5 ≤ M) (hhi : M ≤ 0) :
    |(1 + Real.sqrt (M + 5)) - M| + (1 + Real.sqrt (M + 5)) ^ 2 -
      3 * (1 + Real.sqrt (M + 5)) = 4 := by
  have hr := Real.sqrt_nonneg (M + 5)
  have hs := Real.sq_sqrt (show 0 ≤ M + 5 by linarith)
  rw [abs_of_nonneg (by linarith)]
  nlinarith

theorem upper_parameter_witness (M : ℝ) (hlo : 0 ≤ M) (hhi : M ≤ 8) :
    |(2 - Real.sqrt (8 - M)) - M| + (2 - Real.sqrt (8 - M)) ^ 2 -
      3 * (2 - Real.sqrt (8 - M)) = 4 := by
  have hr := Real.sqrt_nonneg (8 - M)
  have hs := Real.sq_sqrt (show 0 ≤ 8 - M by linarith)
  have hle : 2 - Real.sqrt (8 - M) ≤ M := by
    by_cases hm : 2 ≤ M
    · linarith
    · have hp : 0 ≤ M * (3 - M) := mul_nonneg hlo (by linarith)
      have h := Real.le_sqrt_of_sq_le (show (2 - M) ^ 2 ≤ 8 - M by nlinarith)
      linarith
  rw [abs_of_nonpos (by linarith)]
  nlinarith

theorem real_parameter_feasibility (M : ℝ) :
    (∃ x y z : ℝ, |x - M| + y ^ 2 - 3 * z = 4 ∧
      |y - M| + z ^ 2 - 3 * x = 4 ∧ |z - M| + x ^ 2 - 3 * y = 4) ↔
    -5 ≤ M ∧ M ≤ 8 := by
  constructor
  · rintro ⟨x, y, z, h1, h2, h3⟩
    exact parameter_necessary M x y z h1 h2 h3
  · rintro ⟨hlo, hhi⟩
    by_cases hm : M ≤ 0
    · exact ⟨1 + Real.sqrt (M + 5), 1 + Real.sqrt (M + 5), 1 + Real.sqrt (M + 5),
        lower_parameter_witness M hlo hm, lower_parameter_witness M hlo hm,
        lower_parameter_witness M hlo hm⟩
    · exact ⟨2 - Real.sqrt (8 - M), 2 - Real.sqrt (8 - M), 2 - Real.sqrt (8 - M),
        upper_parameter_witness M (by linarith) hhi,
        upper_parameter_witness M (by linarith) hhi,
        upper_parameter_witness M (by linarith) hhi⟩

theorem lower_endpoint_unique (x y z : ℝ)
    (h1 : |x + 5| + y ^ 2 - 3 * z = 4)
    (h2 : |y + 5| + z ^ 2 - 3 * x = 4)
    (h3 : |z + 5| + x ^ 2 - 3 * y = 4) : x = 1 ∧ y = 1 ∧ z = 1 := by
  have hx := le_abs_self (x + 5)
  have hy := le_abs_self (y + 5)
  have hz := le_abs_self (z + 5)
  have hsq : (x - 1) ^ 2 + (y - 1) ^ 2 + (z - 1) ^ 2 ≤ 0 := by nlinarith
  have hx1 : x = 1 := by nlinarith [sq_nonneg (y - 1), sq_nonneg (z - 1)]
  have hy1 : y = 1 := by nlinarith [sq_nonneg (x - 1), sq_nonneg (z - 1)]
  have hz1 : z = 1 := by nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1)]
  exact ⟨hx1, hy1, hz1⟩

theorem upper_endpoint_unique (x y z : ℝ)
    (h1 : |x - 8| + y ^ 2 - 3 * z = 4)
    (h2 : |y - 8| + z ^ 2 - 3 * x = 4)
    (h3 : |z - 8| + x ^ 2 - 3 * y = 4) : x = 2 ∧ y = 2 ∧ z = 2 := by
  have hx := neg_le_abs (x - 8)
  have hy := neg_le_abs (y - 8)
  have hz := neg_le_abs (z - 8)
  have hsq : (x - 2) ^ 2 + (y - 2) ^ 2 + (z - 2) ^ 2 ≤ 0 := by nlinarith
  have hx2 : x = 2 := by nlinarith [sq_nonneg (y - 2), sq_nonneg (z - 2)]
  have hy2 : y = 2 := by nlinarith [sq_nonneg (x - 2), sq_nonneg (z - 2)]
  have hz2 : z = 2 := by nlinarith [sq_nonneg (x - 2), sq_nonneg (y - 2)]
  exact ⟨hx2, hy2, hz2⟩

theorem source_no_real_solutions :
    ¬ ∃ x y z : ℝ, |x - 2015| + y ^ 2 - 3 * z = 4 ∧
      |y - 2015| + z ^ 2 - 3 * x = 4 ∧ |z - 2015| + x ^ 2 - 3 * y = 4 := by
  rw [real_parameter_feasibility]
  norm_num

theorem solution (x y z : ℤ)
    (h1 : |x - 2015| + y ^ 2 - 3 * z = 4)
    (h2 : |y - 2015| + z ^ 2 - 3 * x = 4)
    (h3 : |z - 2015| + x ^ 2 - 3 * y = 4) :
    x = 2015 ∧ y = 2015 ∧ z = 2015 := by
  exfalso
  apply source_no_real_solutions
  refine ⟨(x : ℝ), (y : ℝ), (z : ℝ), ?_, ?_, ?_⟩
  · exact_mod_cast h1
  · exact_mod_cast h2
  · exact_mod_cast h3
