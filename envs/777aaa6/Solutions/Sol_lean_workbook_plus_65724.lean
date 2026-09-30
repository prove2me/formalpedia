-- Prove2me | solution 1 for lean_workbook_plus_65724
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:50:49.019921+00:00
-- url     : https://prove2.me/submissions/d73fb23c-9f95-4f68-b193-7b7044e9c79c

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

private theorem scaled_formula (f : ℕ → ℕ → ℝ)
    (h0 : ∀ b, f 0 b = 0) (h1 : ∀ a, f a 0 = a)
    (hrec : ∀ a b, (a + b) * f a b = a * f (a - 1) b + b * f a (b - 1)) :
    ∀ a b : ℕ, ((b : ℝ) + 1) * f a b = a := by
  intro a
  induction a with
  | zero => intro b; simp [h0]
  | succ a iha =>
    intro b
    induction b with
    | zero => simp [h1]
    | succ b ihb =>
      have ha := iha (b + 1)
      have hr := hrec (a + 1) (b + 1)
      simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] at ha hr ihb ⊢
      have hc : (((a : ℝ) + 1) + ((b : ℝ) + 1)) *
          ((((b : ℝ) + 1) + 1) * f (a + 1) (b + 1) - ((a : ℝ) + 1)) = 0 := by
        linear_combination ((b : ℝ) + 2) * hr + ((a : ℝ) + 1) * ha +
          ((b : ℝ) + 2) * ihb
      have hpos : (((a : ℝ) + 1) + ((b : ℝ) + 1)) ≠ 0 := by positivity
      exact sub_eq_zero.mp ((mul_eq_zero.mp hc).resolve_left hpos)

theorem closed_form (f : ℕ → ℕ → ℝ)
    (h0 : ∀ b, f 0 b = 0) (h1 : ∀ a, f a 0 = a)
    (hrec : ∀ a b, (a + b) * f a b = a * f (a - 1) b + b * f a (b - 1))
    (a b : ℕ) : f a b = a / ((b : ℝ) + 1) := by
  apply (eq_div_iff (by positivity : (b : ℝ) + 1 ≠ 0)).mpr
  simpa [mul_comm] using scaled_formula f h0 h1 hrec a b

theorem solution (f : ℕ → ℕ → ℝ)
    (h0 : ∀ b, f 0 b = 0) (h1 : ∀ a, f a 0 = a)
    (hrec : ∀ a b, (a + b) * f a b = a * f (a - 1) b + b * f a (b - 1)) :
    f 15 10 = 15 / 11 := by
  convert closed_form f h0 h1 hrec 15 10 using 1 <;> norm_num
