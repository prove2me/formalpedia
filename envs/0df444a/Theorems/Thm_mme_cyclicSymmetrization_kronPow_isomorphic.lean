-- Prove2me | Theorems.Thm_mme_cyclicSymmetrization_kronPow_isomorphic
-- name    : mme_cyclicSymmetrization_kronPow_isomorphic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T05:00:15.783508+00:00
-- url     : https://prove2.me/theorems/d899b6e1-7c36-4aea-acaf-baed2727068e
-- title:
--   Cyclic symmetrization commutes with Kronecker powers
-- statement:
--   Let $X$ be an order-three tensor over a field and let $n\ge0$. Cyclic symmetrization commutes with the $n$-th Kronecker power up to tensor isomorphism:
--
--   $$
--   \bigl(X\otimes\pi(X)\otimes\pi^2(X)\bigr)^{\otimes n}
--   \cong
--   X^{\otimes n}\otimes\pi(X^{\otimes n})\otimes\pi^2(X^{\otimes n}).
--   $$
--
--   Both restriction directions are retained. This is the reassociation and mode-permutation bridge needed to turn a value result proved for the cyclic symmetrization of a powered tensor into a result for a power of the original cyclic symmetrization.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), symmetric tensor value on journal p. 264; standard compatibility of tensor products, powers, and mode permutations.

import Definitions.Def_mme_CW_coupled_value
import Definitions.Def_mme_permutation
import Definitions.Def_mme_rank_bridge

open MME

universe u

theorem mme_cyclicSymmetrization_kronPow_isomorphic
    {K : Type u} [Field K]
    (X : TensorObj K 3) (n : ℕ) :
    TensorObj.Isomorphic
      ((cyclicSymmetrization X).kronPow n)
      (cyclicSymmetrization (X.kronPow n)) := by
  sorry
