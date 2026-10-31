-- Prove2me | solution 1 for KServer.race_kernel_moments
-- status  : ACCEPTED   (prove)
-- author  : @kwal0203
-- created : 2026-10-30T16:53:22.790555+00:00
-- url     : https://prove2.me/submissions/a8ea28d2-be10-4423-8ce1-5a31925c3412

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option autoImplicit false
open scoped BigOperators

private theorem kernel_square (x a b : ℝ) (hab : a + b ≠ 0) :
    b / (a + b) * (x + a) ^ 2 + a / (a + b) * (x - b) ^ 2 = x ^ 2 + a * b := by
  field_simp
  ring

private theorem kernel_fourth (x a b : ℝ) (hab : a + b ≠ 0) :
    b / (a + b) * (x + a) ^ 4 + a / (a + b) * (x - b) ^ 4 =
      x ^ 4 + a * b * (6 * x ^ 2 + 4 * x * (a - b) + a ^ 2 - a * b + b ^ 2) := by
  field_simp
  ring

theorem solution {Ω : Type*} [Fintype Ω] (P : Ω → ℝ)
    (S L R : ℕ → Ω → ℝ) (n : ℕ) (hzero : ∀ ω, S 0 ω = 0)
    (hden : ∀ j < n, ∀ ω, L j ω + R j ω ≠ 0)
    (hstep : ∀ j < n, ∀ f : ℝ → ℝ,
      (∑ ω, P ω * f (S (j + 1) ω)) =
        ∑ ω, P ω * (R j ω / (L j ω + R j ω) * f (S j ω + L j ω) +
          L j ω / (L j ω + R j ω) * f (S j ω - R j ω))) :
    (∑ ω, P ω * S n ω ^ 2) = ∑ j ∈ Finset.range n, ∑ ω, P ω * (L j ω * R j ω) ∧
    (∑ ω, P ω * S n ω ^ 4) = ∑ j ∈ Finset.range n, ∑ ω,
      P ω * (L j ω * R j ω * (6 * S j ω ^ 2 + 4 * S j ω * (L j ω - R j ω) +
        L j ω ^ 2 - L j ω * R j ω + R j ω ^ 2)) := by
  have hsq (j : ℕ) (hj : j < n) :
      (∑ ω, P ω * S (j + 1) ω ^ 2) =
        (∑ ω, P ω * S j ω ^ 2) + ∑ ω, P ω * (L j ω * R j ω) := by
    rw [hstep j hj (fun x => x ^ 2)]
    simp_rw [kernel_square _ _ _ (hden j hj _), mul_add, Finset.sum_add_distrib]
  have hfour (j : ℕ) (hj : j < n) :
      (∑ ω, P ω * S (j + 1) ω ^ 4) =
        (∑ ω, P ω * S j ω ^ 4) + ∑ ω,
          P ω * (L j ω * R j ω * (6 * S j ω ^ 2 + 4 * S j ω * (L j ω - R j ω) +
            L j ω ^ 2 - L j ω * R j ω + R j ω ^ 2)) := by
    rw [hstep j hj (fun x => x ^ 4)]
    simp_rw [kernel_fourth _ _ _ (hden j hj _), mul_add, Finset.sum_add_distrib]
  have hall : ∀ m ≤ n,
      (∑ ω, P ω * S m ω ^ 2) = ∑ j ∈ Finset.range m, ∑ ω, P ω * (L j ω * R j ω) ∧
      (∑ ω, P ω * S m ω ^ 4) = ∑ j ∈ Finset.range m, ∑ ω,
        P ω * (L j ω * R j ω * (6 * S j ω ^ 2 + 4 * S j ω * (L j ω - R j ω) +
          L j ω ^ 2 - L j ω * R j ω + R j ω ^ 2)) := by
    intro m
    induction m with
    | zero => intro _; simp [hzero]
    | succ m ih =>
      intro hm
      obtain ⟨ih2, ih4⟩ := ih (Nat.le_of_succ_le hm)
      constructor
      · rw [hsq m (Nat.lt_of_succ_le hm), ih2, Finset.sum_range_succ]
      · rw [hfour m (Nat.lt_of_succ_le hm), ih4, Finset.sum_range_succ]
  exact hall n le_rfl
