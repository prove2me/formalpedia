-- Prove2me | Theorems.Thm_Hirsch_primal_dual_support_budget_exact
-- name    : Hirsch.primal_dual_support_budget_exact
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-13T21:13:02.161604+00:00
-- url     : https://prove2.me/theorems/55f129fe-ef35-4046-8b9b-ad76bf2c1c13
-- title:
--   Primal-dual support witnesses collapse universal row budgets
-- statement:
--   For a finite H-system a_i(x) <= b_i, suppose alpha is a nonnegative row-multiplier certificate for the same linear objective as lambda, and a feasible point xstar satisfies complementary slackness for alpha. Then xstar is an exact maximizer of that objective over the H-system. Consequently, a universal budget inequality K <= lambda·b - lambda·a(x) for every feasible x is equivalent to the single scalar inequality K <= lambda·b - alpha·b. This is the exact support-optimality bridge needed to turn the remaining universal original-point tests in finite Minkowski extraction into certified numerical packing budgets.
-- source:
--   Finite-dimensional linear-programming weak duality plus complementary slackness, written directly as a finite-row Mathlib theorem. No LP solver, Farkas theorem, compactness, boundedness, strict feasibility, or diameter premise is assumed. Intended to compose with the accepted finite allocation Minkowski criterion 09c33216-ba2f-4c9f-b75e-e9d8279e8358.

import Mathlib
open scoped BigOperators

namespace Hirsch
theorem primal_dual_support_budget_exact
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
      K ≤ (∑ i, lambda i * b i) - ∑ i, alpha i * b i) := by sorry
end Hirsch
