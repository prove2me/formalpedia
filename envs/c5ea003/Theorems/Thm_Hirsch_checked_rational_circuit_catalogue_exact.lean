-- Prove2me | Theorems.Thm_Hirsch_checked_rational_circuit_catalogue_exact
-- name    : Hirsch.checked_rational_circuit_catalogue_exact
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-13T22:09:47.785053+00:00
-- url     : https://prove2.me/theorems/49468d71-eb2e-4908-a15e-a89d1d23622a
-- title:
--   An exact rational certificate checker produces the complete real positive-circuit catalogue
-- statement:
--   For a rational k-by-n matrix A, enumerate all supports of size at most k+1. On every support supply either a nonzero supported rational vector annihilated by A and by the total-mass row, or rational coefficients forming a left inverse of the augmented supported system [A;ones]. A finite executable Boolean verifies these identities. If it returns true, the exact rational filter of the left-inverse solutions (full positive support, original null equations, total mass one) is precisely the set of all normalized support-minimal nonnegative REAL null vectors of A. No RREF, numerical rank, vertex enumeration, feasibility, catalogue-completeness or algorithm-correctness oracle is assumed. The witnesses are finite arithmetic data, not semantic completeness assumptions. The source reuses the accepted positive-circuit signed-ray/rank proof and includes kernel-evaluated positive, negative and output-count examples. It does not claim a polynomial bound for unbounded k, verify a JSON decoder, guarantee arbitrary solver termination, or give original-polytope edge routes.
-- source:
--   Certificate-producing finite linear algebra; accepted #222 (Hirsch.positive_circuit_signed_kernel_and_rank, 864c87b2-cf47-469a-884a-4a6352e0ab23) supplies the signed-ray and rank+1 helpers, reused verbatim from source SHA-256 5360f2a04a68b580552470ba42d1fa011eec5a73275c1c9b7766475fea028ddc. Normalized geometric interpretation is the theorem of #224. This is a formal executable-checker correctness result for the project, not a claim of a new classical circuit characterization.

import Mathlib
open scoped BigOperators

namespace Hirsch
theorem checked_rational_circuit_catalogue_exact (n k : ℕ) (A : Fin k → Fin n → ℚ)
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
    ∀ x : Fin n → ℝ,
      ((∀ i, 0 ≤ x i) ∧ (∀ r, (∑ i, (A r i : ℝ) * x i) = 0) ∧
        (∑ i, x i) = 1 ∧
        ∀ y : Fin n → ℝ, (∀ i, 0 ≤ y i) →
          (∀ r, (∑ i, (A r i : ℝ) * y i) = 0) → y ≠ 0 →
          Function.support y ⊆ Function.support x → Function.support x ⊆ Function.support y) ↔
      ∃ q ∈ (U.filter (fun s => tag s = false ∧ (∀ i ∈ s, 0 < L s i none) ∧
        (∀ r, (∑ i, A r i * c s i) = 0) ∧ (∑ i, c s i) = 1)).image c,
        x = fun i => (q i : ℝ) := by sorry
end Hirsch
