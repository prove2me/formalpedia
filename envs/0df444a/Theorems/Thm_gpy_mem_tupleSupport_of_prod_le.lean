-- Prove2me | Theorems.Thm_gpy_mem_tupleSupport_of_prod_le
-- name    : gpy_mem_tupleSupport_of_prod_le
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-30T02:53:45.631985+00:00
-- url     : https://prove2.me/theorems/a53a12a6-0d72-4acd-af51-eae8d7c9781a
-- title:
--   Support membership is automatic at fixed products
-- statement:
--   At fixed products D ≤ R, a tuple d with 1 ≤ d j at every coordinate and product D lies in the support set of tuples with coordinates in [1, R] and product at most R: the size cutoff is not an extra local constraint at fixed (D, E). Formalization Note: the support set is written out in Mathlib terms, with no local definitions.
-- source:
--   GPY good-count local evaluation, formalized from Mathlib (prime factorization of the good-pair condition)

import Mathlib
open Classical

theorem gpy_mem_tupleSupport_of_prod_le {k : ℕ} {R D : ℕ} (hD : D ≤ R) {d : Fin k → ℕ}
    (h1 : ∀ j, 1 ≤ d j) (hprod : ∏ j, d j = D) :
    d ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
      (fun d => ∏ i, d i ≤ R) := by sorry
