-- Prove2me | Theorems.Thm_gpy_mem_diffPrimeFinset
-- name    : gpy_mem_diffPrimeFinset
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-30T23:00:45.015363+00:00
-- url     : https://prove2.me/theorems/e4d24f85-eb60-4476-a7d8-a5f265a9ff63
-- title:
--   Membership in the finite difference-prime set
-- statement:
--   A prime belongs to the finite set of prime divisors of the nonzero differences |h_i - h_j| for j different from i exactly when it divides some such difference. The set is fixed by the tuple h and the coordinate i alone. Formalization Note: the set is written out as a biUnion over the filtered index set, in Mathlib terms.
-- source:
--   GPY defect control: exact characterizations and exact sum identities for the compatible-but-not-good (defect) pairs

import Mathlib
open Classical

theorem gpy_mem_diffPrimeFinset {k : ℕ} {h : Fin k → ℕ} {i : Fin k}
    {p : ℕ} :
    p ∈ (Finset.univ.filter (fun j : Fin k => j ≠ i)).biUnion
        (fun j => (Int.natAbs ((h i : ℤ) - (h j : ℤ))).primeFactors) ↔
      ∃ j, j ≠ i ∧ p ∈ (Int.natAbs ((h i : ℤ) - (h j : ℤ))).primeFactors := by sorry
