-- Prove2me | Theorems.Thm_XiCountedQPublished_reciprocal_summability_from_count
-- name    : XiCountedQPublished.reciprocal_summability_from_count
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-16T08:31:46.017199+00:00
-- url     : https://prove2.me/theorems/a142139b-f802-479e-913e-4eea9e3ea322
-- title:
--   Reciprocal summability and an explicit bound from sublinear counting
-- statement:
--   Let \(a_j\ge1\), let \(r<1\), and let \(C\in\mathbb R\). Suppose every finite set of indices with \(a_j\le y\) has cardinality at most \(Cy^r\), for every \(y\ge1\). Then
--   \[\sum_j a_j^{-1}\ \text{converges},\qquad \sum_j a_j^{-1}\le\frac{C}{1-r}.\]
--   The counting condition counts indices, including repetitions. Applied to squared zero heights, this supplies the inverse-square summability needed for canonical products and Laplace representations. The condition must be established separately for the sequence of interest.
-- source:
--   Desenvolvimento RH, Ricardo Marangoni Brandao Bueno. PF28 and corrected Branches 2/3. Formalization of classical analytic tools and conditional logarithmic-Q positivity, 2026-11-16. No novelty or RH proof claimed. https://app.notion.com/p/41a98395ac6e8160a225d82e667ec8e4

import Mathlib
open MeasureTheory Set Filter Topology
open scoped BigOperators

theorem XiCountedQPublished.reciprocal_summability_from_count (a : ℕ → ℝ) (ha : ∀ j, 1 ≤ a j)
    (C r : ℝ) (hr : r < 1)
    (hcount : ∀ y ≥ (1 : ℝ), ∀ F : Finset ℕ,
      (∀ j ∈ F, a j ≤ y) → (F.card : ℝ) ≤ C*y^r) :
    Summable (fun j => (a j)⁻¹) ∧ (∑' j, (a j)⁻¹) ≤ C/(1-r) := by sorry
