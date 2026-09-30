-- Prove2me | solution 1 for Hirsch.finite_allocation_pointwise_primal_dual_budgets
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-13T21:40:47.807956+00:00
-- url     : https://prove2.me/submissions/930c75c8-3cc5-4ea0-abaf-a01012f50709

import Mathlib

open Set
open scoped BigOperators

/-- Collapse an already-established finite allocation pointwise criterion to one
exact scalar budget per multiplier using original-H primal/dual witnesses. -/
theorem solution
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (m k : ℕ) (a : Fin m → E →L[ℝ] ℝ)
    (G : (Fin k → ℝ) →L[ℝ] E)
    (c : Finset (Fin m ⊕ Option (Fin k)) → ((Fin m ⊕ Option (Fin k)) → ℝ))
    (b h : Fin m → ℝ) (t : ℝ)
    (hpointwise :
      (({x : E | ∀ i, a i x ≤ b i} =
        {x : E | ∃ p : E, (∀ i, a i p ≤ b i - h i) ∧
          ∃ θ : Fin k → ℝ, (∀ j, 0 ≤ θ j) ∧ (∑ j, θ j) ≤ t ∧ p + G θ = x}) ↔
        (∀ x : E, (∀ i, a i x ≤ b i) → ∀ s,
          0 ≤ (∑ i, c s (.inl i) * (b i - a i x - h i)) + c s (.inr none) * t)))
    (alpha : Finset (Fin m ⊕ Option (Fin k)) → Fin m → ℝ)
    (xstar : Finset (Fin m ⊕ Option (Fin k)) → E)
    (halpha : ∀ s i, 0 ≤ alpha s i)
    (hxstar : ∀ s i, a i (xstar s) ≤ b i)
    (hforms : ∀ s, ∀ x : E,
      (∑ i, c s (.inl i) * a i x) = ∑ i, alpha s i * a i x)
    (hcomp : ∀ s i, alpha s i * (b i - a i (xstar s)) = 0) :
    (({x : E | ∀ i, a i x ≤ b i} =
      {x : E | ∃ p : E, (∀ i, a i p ≤ b i - h i) ∧
        ∃ θ : Fin k → ℝ, (∀ j, 0 ≤ θ j) ∧ (∑ j, θ j) ≤ t ∧ p + G θ = x}) ↔
      ∀ s,
        (∑ i, c s (.inl i) * h i) - c s (.inr none) * t ≤
          (∑ i, c s (.inl i) * b i) - ∑ i, alpha s i * b i) := by
  classical
  rw [hpointwise]
  constructor
  · intro hall s
    have hstar :
        (∑ i, alpha s i * a i (xstar s)) = ∑ i, alpha s i * b i := by
      apply Finset.sum_congr rfl
      intro i hi
      have hc := hcomp s i
      calc
        alpha s i * a i (xstar s) =
            alpha s i * b i - alpha s i * (b i - a i (xstar s)) := by ring
        _ = alpha s i * b i := by rw [hc]; ring
    have hs := hall (xstar s) (hxstar s) s
    have hform := hforms s (xstar s)
    simp only [mul_sub, Finset.sum_sub_distrib] at hs
    linarith
  · intro hscalar x hx s
    have hupper :
        (∑ i, alpha s i * a i x) ≤ ∑ i, alpha s i * b i := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hx i) (halpha s i)
    have hform := hforms s x
    have hs := hscalar s
    simp only [mul_sub, Finset.sum_sub_distrib]
    linarith

#print axioms solution
