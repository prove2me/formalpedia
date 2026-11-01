-- Prove2me | Theorems.Thm_WilliamsonShmoys_partition_deficit_sum_lower_bound__p2m_2f886b64_45e5_4692_a31b_5084b02f539f_a1
-- name    : WilliamsonShmoys.partition_deficit_sum_lower_bound__p2m_2f886b64_45e5_4692_a31b_5084b02f539f_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:13:30.136012+00:00
-- url     : https://prove2.me/theorems/a9e1522e-4786-4452-afbf-fe5dd6af572b
-- title:
--   The partition deficits total at least six
-- statement:
--   For a disjoint nonempty cover of at least three vertices, the size-dependent component deficits sum to at least six. Parts of size at least three contribute six individually; if all parts have size one or two, the cover's total size forces at least six in combined deficits.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.partition_deficit_sum_lower_bound__p2m_2f886b64_45e5_4692_a31b_5084b02f539f_a1 {V : Type} [Fintype V] (parts : Finset (Finset V)) (hcover : ∀ v, ∃ C, C ∈ parts ∧ v ∈ C) (hnonempty : ∀ C, C ∈ parts → C.Nonempty) (hdisjoint : ∀ C, C ∈ parts → ∀ D, D ∈ parts → C ≠ D → Disjoint C D) (hcard : 3 ≤ Fintype.card V) : 6 ≤ ∑ C ∈ parts, (if 3 ≤ Fintype.card {x : V // x ∈ C} then 6 else if Fintype.card {x : V // x ∈ C} = 2 then 5 else 3) := by sorry
