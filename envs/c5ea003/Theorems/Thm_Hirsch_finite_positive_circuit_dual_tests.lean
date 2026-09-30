-- Prove2me | Theorems.Thm_Hirsch_finite_positive_circuit_dual_tests
-- name    : Hirsch.finite_positive_circuit_dual_tests
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-13T19:42:38.553986+00:00
-- url     : https://prove2.me/theorems/8f3c4cc7-be73-4ecf-9e17-816c710e20d7
-- title:
--   Finite positive-circuit completeness for nonnegative-kernel dual tests
-- statement:
--   For any real linear map A from R^n to R^k, there is a fixed family c indexed by the subsets of the n coordinate indices. Each c_s is either zero or a nonzero nonnegative null vector of A with support exactly s, minimal among supports of nonzero nonnegative null vectors. The family depends on A but not on a subsequent real linear functional b. For every b, nonnegativity of b on the whole nonnegative kernel of A is equivalent to nonnegativity on all the c_s. Thus one representative per positive-circuit support suffices for every linear dual test. Unused support slots are zero; at most 2^n slots are available. The statement neither assumes a circuit-generation/Farkas theorem nor asserts a polynomial circuit count, the sharper rank(A)+1 support bound, an executable enumerator, geometric Minkowski reconstruction, or Polynomial Hirsch.
-- source:
--   Classical support-elimination proof, formalized directly using finite minimum ratios and least support cardinality. Mathlib pin c5ea00351c28e24afc9f0f84379aa41082b1188f; Finset.exists_min_image in Mathlib/Data/Finset/Max.lean and finite-support cardinality lemmas. This is a reusable formal interface, not a claim of classical mathematical novelty. Complementary to accepted compact-dual Minkowski theorem a6e2a38d-00e3-46d6-b232-7cddee5e30e1; that theorem is not an imported proof dependency of this algebraic lemma.

import Mathlib
open scoped BigOperators

namespace Hirsch
theorem finite_positive_circuit_dual_tests (n k : ℕ)
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin k → ℝ)) :
    ∃ c : Finset (Fin n) → (Fin n → ℝ),
      (∀ s, c s = 0 ∨
        ((∀ i, 0 ≤ c s i) ∧ A (c s) = 0 ∧ c s ≠ 0 ∧
          Function.support (c s) = (s : Set (Fin n)) ∧
          ∀ y : Fin n → ℝ, (∀ i, 0 ≤ y i) → A y = 0 → y ≠ 0 →
            Function.support y ⊆ Function.support (c s) →
            Function.support (c s) ⊆ Function.support y)) ∧
      ∀ b : (Fin n → ℝ) →ₗ[ℝ] ℝ,
        (∀ x : Fin n → ℝ, (∀ i, 0 ≤ x i) → A x = 0 → 0 ≤ b x) ↔
          ∀ s, 0 ≤ b (c s) := by sorry
end Hirsch
