-- Prove2me | Theorems.Thm_gpy_squarefree_of_mem_prod
-- name    : gpy_squarefree_of_mem_prod
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-30T02:47:30.302948+00:00
-- url     : https://prove2.me/theorems/a9bc29bf-9148-4f29-a43d-d8081ee55fa5
-- title:
--   A factor of a squarefree product is squarefree
-- statement:
--   If the product over a tuple d is squarefree, then each coordinate d j is squarefree. Formalization Note: the statement uses only Mathlib terms.
-- source:
--   GPY good-count local evaluation, formalized from Mathlib (prime factorization of the good-pair condition)

import Mathlib
open Classical

theorem gpy_squarefree_of_mem_prod {k : ℕ} {d : Fin k → ℕ} {j : Fin k}
    (hsq : Squarefree (∏ i, d i)) : Squarefree (d j) := by sorry
