-- Prove2me | Theorems.Thm_Hirsch_checked_rational_catalogue_dual_tests
-- name    : Hirsch.checked_rational_catalogue_dual_tests
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-13T23:39:12.551563+00:00
-- url     : https://prove2.me/theorems/3999b5a0-22c8-44a5-9886-6838b03fd07f
-- title:
--   A checked rational circuit catalogue certifies every real linear dual test
-- statement:
--   For a rational k-by-n matrix A, use exactly the finite Boolean support audit and rational output filter from the accepted checked-circuit-catalogue theorem. If the arithmetic audit returns true, then for EVERY real linear functional B, nonnegativity of B on ALL nonnegative real null vectors of A is equivalent to nonnegativity of B on the actual emitted rational catalogue after casting to the reals. The catalogue is fixed before B is chosen. This formally connects executable catalogue completeness to the universal nonnegative-kernel dual tests used in allocation. No semantic catalogue-completeness, circuit-generation, Farkas, nonempty-section, full-rank, or diameter hypothesis is assumed. This theorem does not yet reindex the allocation rows or conclude a whole-set Minkowski equality or a graph-diameter bound.
-- source:
--   Composition of accepted PR #229 checked rational catalogue exactness (theorem 49468d71-eb2e-4908-a15e-a89d1d23622a) and the accepted #218 negative-positive-circuit support-pruning core, reused verbatim from accepted #219 artifact 10324553494. The new argument proves real normalization and support transport into the actual checked catalogue. No classical novelty claim.

import Mathlib
open scoped BigOperators

namespace Hirsch
theorem checked_rational_catalogue_dual_tests (n k : ℕ) (A : Fin k → Fin n → ℚ)
    (tag : Finset (Fin n) → Bool)
    (L : Finset (Fin n) → Fin n → Option (Fin k) → ℚ)
    (z : Finset (Fin n) → Fin n → ℚ) :
    let U := (Finset.range (k + 2)).biUnion
      (fun r => (Finset.univ : Finset (Fin n)).powersetCard r)
    let c : Finset (Fin n) → Fin n → ℚ := fun s i => if i ∈ s then L s i none else 0
    decide (∀ s ∈ U, if tag s then
        (∃ i, z s i ≠ 0) ∧ (∀ i, i ∉ s → z s i = 0) ∧
          (∀ r, (∑ i, A r i * z s i) = 0) ∧ (∑ i, z s i) = 0
      else ∀ i ∈ s, ∀ j ∈ s,
        (∑ r, L s i (some r) * A r j) + L s i none = if i = j then 1 else 0) = true →
    ∀ B : (Fin n → ℝ) →ₗ[ℝ] ℝ,
      (∀ w : Fin n → ℝ, (∀ i, 0 ≤ w i) →
        (∀ r, (∑ i, (A r i : ℝ) * w i) = 0) → 0 ≤ B w) ↔
      ∀ q ∈ (U.filter (fun s => tag s = false ∧ (∀ i ∈ s, 0 < L s i none) ∧
        (∀ r, (∑ i, A r i * c s i) = 0) ∧ (∑ i, c s i) = 1)).image c,
        0 ≤ B (fun i => (q i : ℝ)) := by sorry
end Hirsch
