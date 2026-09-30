-- Prove2me | Theorems.Thm_Hirsch_positive_circuit_signed_kernel_and_rank
-- name    : Hirsch.positive_circuit_signed_kernel_and_rank
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-13T21:13:21.712744+00:00
-- url     : https://prove2.me/theorems/864c87b2-cf47-469a-884a-4a6352e0ab23
-- title:
--   Positive circuit signed-kernel characterization and sharp rank-plus-one support bound
-- statement:
--   Let A:R^n -> R^k be real linear and x be a nonzero nonnegative vector with A x=0. Minimality of the support of x among nonzero nonnegative kernel vectors is equivalent to: every signed kernel vector supported on supp(x) is a real scalar multiple of x. Under this minimality condition, the support of x has cardinality at most dim(range(A))+1. There is no full-rank, simplicity, boundedness or generator-independence hypothesis. This is the sharp support cutoff and exact one-dimensional-kernel criterion needed after the accepted finite positive-circuit tests; it does not establish executable row-reduction correctness or Polynomial Hirsch.
-- source:
--   Classical elementary positive-dependence and rank argument; standalone formalization of the rank+1 obligation explicitly left open by accepted PR #218 in jjoshua2/prove2me-work. Uses Mathlib Finset.exists_min_image, LinearMap.finrank_le_finrank_of_injective, and Module.finrank_prod at c5ea00351c28e24afc9f0f84379aa41082b1188f. No claim of historical novelty.

import Mathlib
open scoped BigOperators

namespace Hirsch
theorem positive_circuit_signed_kernel_and_rank (n k : ℕ)
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin k → ℝ)) (x : Fin n → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hAx : A x = 0) (hxne : x ≠ 0) :
    ((∀ y : Fin n → ℝ, (∀ i, 0 ≤ y i) → A y = 0 → y ≠ 0 →
        Function.support y ⊆ Function.support x →
        Function.support x ⊆ Function.support y) ↔
      (∀ z : Fin n → ℝ, A z = 0 →
        Function.support z ⊆ Function.support x → ∃ t : ℝ, z = t • x)) ∧
    ((∀ y : Fin n → ℝ, (∀ i, 0 ≤ y i) → A y = 0 → y ≠ 0 →
        Function.support y ⊆ Function.support x →
        Function.support x ⊆ Function.support y) →
      Nat.card {i : Fin n // x i ≠ 0} ≤ Module.finrank ℝ (LinearMap.range A) + 1) := by sorry
end Hirsch
