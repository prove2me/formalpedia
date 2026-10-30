-- Prove2me | Theorems.Thm_gpy_pairwise_coprime_of_squarefree_prod
-- name    : gpy_pairwise_coprime_of_squarefree_prod
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T20:25:46.798551+00:00
-- url     : https://prove2.me/theorems/44e36ea9-ecc2-4bf7-8866-853e74892a18
-- title:
--   Pairwise coprimality on squarefree-product support
-- statement:
--   If the product of a tuple of positive integers is squarefree, then any two distinct coordinates are coprime: their gcd squares-divides the product, and squarefreeness forces it to be 1.
-- source:
--   GPY Selberg fiber bound for tuple weights, formalized from Mathlib (squarefree products, pairwise coprimality, and fiber counting)

import Mathlib
open Classical

theorem gpy_pairwise_coprime_of_squarefree_prod {k : ℕ} {d : Fin k → ℕ}
    (_hd1 : ∀ i, 1 ≤ d i) (hsq : Squarefree (∏ i, d i))
    {i j : Fin k} (hij : i ≠ j) :
    Nat.Coprime (d i) (d j) := by sorry
