-- Prove2me | Theorems.Thm_gpy_combined_lcm_eq
-- name    : gpy_combined_lcm_eq
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T20:25:53.965396+00:00
-- url     : https://prove2.me/theorems/fa270577-4e24-414a-b206-422a16f14b5c
-- title:
--   The combined modulus is the lcm of the products
-- statement:
--   On squarefree-product support, the combined modulus (the lcm over coordinates of the coordinatewise lcms) equals the lcm of the two coordinate products.
-- source:
--   GPY Selberg fiber bound for tuple weights, formalized from Mathlib (squarefree products, pairwise coprimality, and fiber counting)

import Mathlib
open Classical

theorem gpy_combined_lcm_eq {k : ℕ} {d e : Fin k → ℕ}
    (hd1 : ∀ i, 1 ≤ d i) (he1 : ∀ i, 1 ≤ e i)
    (hsqd : Squarefree (∏ i, d i)) (hsqe : Squarefree (∏ i, e i)) :
    Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))
      = Nat.lcm (∏ i, d i) (∏ i, e i) := by sorry
