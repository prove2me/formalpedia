-- Prove2me | solution 1 for Hirsch.primal_dual_support_budget_exact
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-13T21:14:42.190635+00:00
-- url     : https://prove2.me/submissions/7f7c3497-e656-4baf-8b14-22ae1059adad

import Mathlib
open scoped BigOperators
set_option autoImplicit false
noncomputable section

theorem solution
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]
    (a : ι → E →L[ℝ] ℝ) (b lambda alpha : ι → ℝ)
    (xstar : E) (K : ℝ)
    (halpha : ∀ i, 0 ≤ alpha i)
    (hxstar : ∀ i, a i xstar ≤ b i)
    (hforms : ∀ x : E,
      (∑ i, lambda i * a i x) = ∑ i, alpha i * a i x)
    (hcomp : ∀ i, alpha i * (b i - a i xstar) = 0) :
    ((∀ x : E, (∀ i, a i x ≤ b i) →
        K ≤ (∑ i, lambda i * b i) - ∑ i, lambda i * a i x) ↔
      K ≤ (∑ i, lambda i * b i) - ∑ i, alpha i * b i) := by
  have hstar :
      (∑ i, alpha i * a i xstar) = ∑ i, alpha i * b i := by
    apply Finset.sum_congr rfl
    intro i hi
    have hc := hcomp i
    calc
      alpha i * a i xstar =
          alpha i * b i - alpha i * (b i - a i xstar) := by ring
      _ = alpha i * b i := by rw [hc]; ring
  constructor
  · intro h
    have hs := h xstar hxstar
    rw [hforms xstar, hstar] at hs
    exact hs
  · intro h x hx
    have hupper :
        (∑ i, alpha i * a i x) ≤ ∑ i, alpha i * b i := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hx i) (halpha i)
    rw [hforms x]
    linarith

#print axioms solution
