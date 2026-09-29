-- Prove2me | solution 1 for cos_shift_decompose
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-09T13:26:27.184565+00:00
-- url     : https://prove2.me/submissions/b9ca786c-c263-4b31-93a4-b948af651229

import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Polynomial

namespace CosShiftDecompose

/-- Auxiliary: `cos_shift_decompose` with the degree bound `≤ n` in the hypothesis,
so we can do induction on `n`. Also tracks `E(1) = Q(cos φ)`. -/
theorem aux (n : ℕ) : ∀ (Q : Polynomial ℝ) (φ : ℝ), Q.natDegree ≤ n →
    ∃ E P : Polynomial ℝ, E.natDegree ≤ Q.natDegree ∧
      (P.natDegree + 1 ≤ Q.natDegree ∨ P = 0) ∧
      (∀ θ : ℝ, Q.eval (Real.cos (φ + θ)) = E.eval (Real.cos θ) + P.eval (Real.cos θ) * Real.sin θ) ∧
      E.eval 1 = Q.eval (Real.cos φ) ∧
      P.eval 1 = -Real.sin φ * Q.derivative.eval (Real.cos φ) := by
  induction n with
  | zero =>
    -- Q is constant.
    intro Q φ hQdeg
    have hQ0 : Q.natDegree = 0 := Nat.le_zero.mp hQdeg
    obtain ⟨a, ha⟩ := Polynomial.natDegree_eq_zero.mp hQ0
    refine ⟨C a, 0, ?_, Or.inr rfl, ?_, ?_, ?_⟩
    · rw [Polynomial.natDegree_C]; omega
    · intro θ; rw [← ha]; simp
    · rw [← ha]; simp
    · rw [← ha]; simp
  | succ m ih =>
    intro Q φ hQdeg
    rcases Nat.lt_or_ge m Q.natDegree with hgt | hle
    swap
    · exact ih Q φ hle
    -- Q.natDegree = m + 1.
    have hQeq : Q.natDegree = m + 1 := le_antisymm hQdeg hgt
    have hQ1pos : 1 ≤ Q.natDegree := by omega
    -- Decompose Q = X * Q.divX + C (Q.coeff 0).
    set a := Q.coeff 0 with ha_def
    set Q₁ := Q.divX with hQ1_def
    have hXmul : X * Q₁ + C a = Q := Polynomial.X_mul_divX_add Q
    -- Q₁ ≠ 0 and natDegree Q₁ = m.
    have hQ1ne : Q₁ ≠ 0 := by
      intro hQ10
      rw [hQ10, mul_zero, zero_add] at hXmul
      rw [← hXmul, Polynomial.natDegree_C] at hQeq
      omega
    have hQ1deg : Q₁.natDegree ≤ m := by
      have hX : (X * Q₁).natDegree = 1 + Q₁.natDegree := by
        rw [Polynomial.natDegree_mul (Polynomial.X_ne_zero) hQ1ne, Polynomial.natDegree_X]
      have hlt : (C a : ℝ[X]).natDegree < (X * Q₁).natDegree := by
        rw [Polynomial.natDegree_C, hX]; omega
      have heq : Q.natDegree = (X * Q₁).natDegree := by
        rw [← hXmul]
        exact Polynomial.natDegree_add_eq_left_of_natDegree_lt hlt
      rw [heq, hX] at hQeq
      omega
    -- IH applied to Q₁.
    obtain ⟨E₁, P₁, hE₁deg, hP₁deg, hident₁, hE₁1, hP₁1⟩ := ih Q₁ φ hQ1deg
    -- Define E, P.
    set E : Polynomial ℝ := C a + C (Real.cos φ) * X * E₁ - C (Real.sin φ) * (1 - X^2) * P₁ with hE_def
    set P : Polynomial ℝ := C (Real.cos φ) * X * P₁ - C (Real.sin φ) * E₁ with hP_def
    refine ⟨E, P, ?_, ?_, ?_, ?_, ?_⟩
    · -- deg E ≤ deg Q.
      rw [hE_def]
      have h1 : (C a : Polynomial ℝ).natDegree ≤ Q.natDegree := by
        rw [Polynomial.natDegree_C]; omega
      have h2 : (C (Real.cos φ) * X * E₁).natDegree ≤ Q.natDegree := by
        calc (C (Real.cos φ) * X * E₁).natDegree ≤ (C (Real.cos φ) * X).natDegree + E₁.natDegree :=
              Polynomial.natDegree_mul_le
          _ ≤ 1 + E₁.natDegree := by
              apply Nat.add_le_add_right
              calc (C (Real.cos φ) * X).natDegree ≤ (C (Real.cos φ)).natDegree + (X : ℝ[X]).natDegree :=
                    Polynomial.natDegree_mul_le
                _ ≤ 0 + 1 := by rw [Polynomial.natDegree_C, Polynomial.natDegree_X]
                _ = 1 := by ring
          _ ≤ 1 + Q₁.natDegree := by omega
          _ ≤ Q.natDegree := by omega
      have h3 : (C (Real.sin φ) * (1 - X^2) * P₁).natDegree ≤ Q.natDegree := by
        rcases hP₁deg with hP₁ | hP₁
        · calc (C (Real.sin φ) * (1 - X^2) * P₁).natDegree ≤ (C (Real.sin φ) * (1 - X^2)).natDegree + P₁.natDegree :=
                Polynomial.natDegree_mul_le
            _ ≤ 2 + P₁.natDegree := by
                apply Nat.add_le_add_right
                calc (C (Real.sin φ) * (1 - X^2)).natDegree ≤ (C (Real.sin φ)).natDegree + ((1:ℝ[X]) - X^2).natDegree :=
                      Polynomial.natDegree_mul_le
                  _ ≤ 0 + 2 := by
                      apply add_le_add
                      · rw [Polynomial.natDegree_C]
                      · calc ((1:ℝ[X]) - X^2).natDegree ≤ max (1:ℝ[X]).natDegree ((X:ℝ[X])^2).natDegree :=
                              Polynomial.natDegree_sub_le _ _
                          _ ≤ 2 := by rw [Polynomial.natDegree_one, Polynomial.natDegree_X_pow]; omega
                  _ = 2 := by ring
            _ ≤ 2 + (Q₁.natDegree - 1) := by omega
            _ ≤ Q.natDegree := by omega
        · rw [hP₁, mul_zero, Polynomial.natDegree_zero]; omega
      calc (C a + C (Real.cos φ) * X * E₁ - C (Real.sin φ) * (1 - X^2) * P₁).natDegree
          ≤ max (C a + C (Real.cos φ) * X * E₁).natDegree (C (Real.sin φ) * (1 - X^2) * P₁).natDegree :=
            Polynomial.natDegree_sub_le _ _
        _ ≤ max (max (C a : Polynomial ℝ).natDegree (C (Real.cos φ) * X * E₁).natDegree)
              (C (Real.sin φ) * (1 - X^2) * P₁).natDegree := by
            apply max_le_max _ le_rfl
            exact Polynomial.natDegree_add_le _ _
        _ ≤ Q.natDegree := by
            apply max_le (max_le h1 h2) h3
    · -- deg P + 1 ≤ deg Q or P = 0.
      by_cases hP0 : P = 0
      · right; exact hP0
      left
      rw [hP_def]
      have h1 : (C (Real.cos φ) * X * P₁).natDegree ≤ Q.natDegree - 1 := by
        rcases hP₁deg with hP₁ | hP₁
        · calc (C (Real.cos φ) * X * P₁).natDegree ≤ (C (Real.cos φ) * X).natDegree + P₁.natDegree :=
                Polynomial.natDegree_mul_le
            _ ≤ 1 + P₁.natDegree := by
                apply Nat.add_le_add_right
                calc (C (Real.cos φ) * X).natDegree ≤ (C (Real.cos φ)).natDegree + (X : ℝ[X]).natDegree :=
                      Polynomial.natDegree_mul_le
                  _ ≤ 1 := by rw [Polynomial.natDegree_C, Polynomial.natDegree_X]
            _ ≤ 1 + (Q₁.natDegree - 1) := by omega
            _ ≤ Q.natDegree - 1 := by omega
        · rw [hP₁, mul_zero, Polynomial.natDegree_zero]; omega
      have h2 : (C (Real.sin φ) * E₁).natDegree ≤ Q.natDegree - 1 := by
        calc (C (Real.sin φ) * E₁).natDegree ≤ E₁.natDegree := Polynomial.natDegree_C_mul_le _ _
          _ ≤ Q₁.natDegree := hE₁deg
          _ ≤ Q.natDegree - 1 := by omega
      calc (C (Real.cos φ) * X * P₁ - C (Real.sin φ) * E₁).natDegree + 1
          ≤ max (C (Real.cos φ) * X * P₁).natDegree (C (Real.sin φ) * E₁).natDegree + 1 := by
            exact Nat.add_le_add_right (Polynomial.natDegree_sub_le _ _) 1
        _ ≤ (Q.natDegree - 1) + 1 := by
            exact Nat.add_le_add_right (max_le h1 h2) 1
        _ ≤ Q.natDegree := by omega
    · -- The identity.
      intro θ
      have hc := Real.cos_add φ θ
      have hident := hident₁ θ
      have hsc := Real.sin_sq_add_cos_sq θ
      rw [← hXmul]
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
        hE_def, hP_def, Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_pow]
      rw [hident, hc]
      have hsub : (1 : ℝ) - (Real.cos θ)^2 = (Real.sin θ)^2 := by nlinarith [hsc]
      rw [hsub]
      ring
    · -- E(1) = Q(cos φ).
      rw [hE_def, ← hXmul]
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
        Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_pow, one_pow]
      rw [hE₁1]
      ring
    · -- P(1) = -sin φ Q'(cos φ).
      rw [hP_def, ← hXmul]
      have hQderiv : (X * Q₁ + C a).derivative = Q₁ + X * Q₁.derivative := by
        rw [Polynomial.derivative_add, Polynomial.derivative_C, add_zero, Polynomial.derivative_mul,
          Polynomial.derivative_X, one_mul]
      simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
        hQderiv, Polynomial.eval_add, one_mul]
      rw [hP₁1, hE₁1]
      ring

end CosShiftDecompose

open CosShiftDecompose

theorem solution : cos_shift_decompose := by
  intro Q φ
  obtain ⟨E, P, h1, h2, h3, _, h5⟩ := aux Q.natDegree Q φ le_rfl
  exact ⟨E, P, h1, h2, h3, h5⟩
