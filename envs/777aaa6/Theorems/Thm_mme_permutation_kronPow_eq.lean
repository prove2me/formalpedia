-- Prove2me | Theorems.Thm_mme_permutation_kronPow_eq
-- name    : mme_permutation_kronPow_eq
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T04:59:22.764059+00:00
-- url     : https://prove2.me/theorems/750e36db-9ca0-47b9-9ca4-1240c4b0c483
-- title:
--   Mode permutations commute with Kronecker powers
-- statement:
--   Let $T$ be a finite-dimensional tensor of order $d$ over a field, let $\sigma$ permute its modes, and let $n\ge 0$. With recursive Kronecker powers and the same mode-reindexing convention on both sides,
--   $$\sigma(T^{\otimes n})=(\sigma T)^{\otimes n}.$$
--   This is equality of tensor objects and can be used to transport coordinate-dependent constructions through a mode permutation.
-- source:
--   Naturality of tensor mode reindexing under Kronecker products and modewise linear maps.

import Definitions.Def_mme_permutation

open MME PiTensorProduct
universe u
set_option autoImplicit false

theorem mme_permutation_kronPow_eq {K : Type u} [Field K] {d : ℕ}
    (e : Equiv.Perm (Fin d)) (X : TensorObj K d) (n : ℕ) :
    TensorObj.permObj e (X.kronPow n) = (TensorObj.permObj e X).kronPow n := by sorry
