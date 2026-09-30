-- Prove2me | solution 1 for congruent_number_problem
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:47:58.937085+00:00
-- url     : https://prove2.me/submissions/f88c646e-e01f-4c1b-9429-f7a40c784b1c

import Mathlib

-- Source module: Main.lean
namespace CongruentNumberCorrespondence

theorem rational_correspondence (N : ℚ) (hN : 0 < N) :
    (∃ a b c : ℚ, 0 < a ∧ 0 < b ∧ 0 < c ∧
      a ^ 2 + b ^ 2 = c ^ 2 ∧ a * b / 2 = N) ↔
    (∃ x y : ℚ, y ^ 2 = x ^ 3 - N ^ 2 * x ∧ y ≠ 0) := by
  constructor
  · rintro ⟨a, b, c, ha, _, hc, hpyth, harea⟩
    refine ⟨a * (a + c) / 2, a ^ 2 * (a + c) / 2, ?_, ?_⟩
    · rw [← harea]
      linear_combination (a ^ 3 * (a + c) / 8) * hpyth
    · exact ne_of_gt (div_pos (mul_pos (sq_pos_of_pos ha) (add_pos ha hc))
        (by norm_num))
  · rintro ⟨x, y, hcurve, hy⟩
    let A : ℚ := (x ^ 2 - N ^ 2) / y
    let B : ℚ := 2 * N * x / y
    let C : ℚ := (x ^ 2 + N ^ 2) / y
    have hpyth : A ^ 2 + B ^ 2 = C ^ 2 := by
      dsimp [A, B, C]
      ring
    have hfactor : x * (x ^ 2 - N ^ 2) = y ^ 2 := by
      nlinarith [hcurve]
    have harea : A * B / 2 = N := by
      calc
        A * B / 2 = N * (x * (x ^ 2 - N ^ 2)) / y ^ 2 := by
          dsimp [A, B]
          ring
        _ = N := by
          rw [hfactor]
          exact mul_div_cancel_right₀ N (pow_ne_zero 2 hy)
    have hAB : 0 < A * B := by linarith
    have hA : A ≠ 0 := by
      intro h
      simp [h] at hAB
    have hB : B ≠ 0 := by
      intro h
      simp [h] at hAB
    have hC : C ≠ 0 := by
      intro h
      have hAsq := sq_pos_of_ne_zero hA
      have hBsq := sq_nonneg B
      rw [h] at hpyth
      nlinarith
    refine ⟨|A|, |B|, |C|, abs_pos.mpr hA, abs_pos.mpr hB,
      abs_pos.mpr hC, ?_, ?_⟩
    · simpa only [sq_abs] using hpyth
    · rw [← abs_mul, abs_of_pos hAB]
      exact harea

end CongruentNumberCorrespondence

theorem solution (n : ℕ) (hn : 0 < n)
    (hsqfree : Squarefree n) :
    (∃ a b c : ℚ, 0 < a ∧ 0 < b ∧ 0 < c ∧ a ^ 2 + b ^ 2 = c ^ 2 ∧ a * b / 2 = n) ↔
    (∃ x y : ℚ, y ^ 2 = x ^ 3 - (n : ℚ) ^ 2 * x ∧ y ≠ 0) := by
  clear hsqfree
  exact CongruentNumberCorrespondence.rational_correspondence (n : ℚ)
    (by exact_mod_cast hn)

#check @solution
#print axioms solution
