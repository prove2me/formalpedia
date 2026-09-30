-- Prove2me | Theorems.Thm_Hirsch_finite_allocation_pointwise_primal_dual_budgets
-- name    : Hirsch.finite_allocation_pointwise_primal_dual_budgets
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-13T21:40:45.501682+00:00
-- url     : https://prove2.me/theorems/2c1c4631-ba41-4cff-aa3b-d4ef1ce80a46
-- title:
--   Collapse finite allocation pointwise tests to exact primal-dual budgets
-- statement:
--   Fix a finite family of allocation multipliers $c_s=(\lambda_s,\mu_s,\nu_s)$ for a candidate summand and suppose an already-established pointwise criterion says that whole-set Minkowski reconstruction is equivalent to
--
--   $$
--   0\le\sum_i\lambda_{s,i}(b_i-a_i(x)-h_i)+\nu_s t
--   $$
--
--   for every original feasible point $x$ and every multiplier $s$. For each $s$, suppose we are also given a feasible sharp point $x_s^*$ and nonnegative original-row weights $\alpha_s$ representing the same linear objective as $\lambda_s$, with complementary slackness at $x_s^*$. Then whole-set reconstruction is equivalent to the finite scalar family
--
--   $$
--   \sum_i\lambda_{s,i}h_i-\nu_s t\le\sum_i\lambda_{s,i}b_i-\sum_i\alpha_{s,i}b_i\qquad\text{for every }s.
--   $$
--
--   This is the exact adapter from the accepted finite-allocation pointwise criterion to original-H primal/dual support budgets. It does not construct the finite multiplier family or the primal/dual witnesses, certify an optimizer, discover a summand, or bound graph diameter.
-- source:
--   Formal adapter for the conclusions of Prove2Me theorem Hirsch.finite_allocation_minkowski_criterion (09c33216-ba2f-4c9f-b75e-e9d8279e8358) and the weak-duality/complementary-slackness principle formalized by Hirsch.primal_dual_support_budget_exact (55f129fe-ef35-4046-8b9b-ad76bf2c1c13).

import Mathlib
open Set
open scoped BigOperators

namespace Hirsch
theorem finite_allocation_pointwise_primal_dual_budgets
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
          (∑ i, c s (.inl i) * b i) - ∑ i, alpha s i * b i) := by sorry
end Hirsch
