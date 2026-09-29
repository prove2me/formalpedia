-- Prove2me | Theorems.Thm_mme_kronPow_kronPow_isomorphic
-- name    : mme_kronPow_kronPow_isomorphic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T16:08:04.05601+00:00
-- url     : https://prove2.me/theorems/b2b1af28-1c51-42a4-a376-46a8f159b030
-- title:
--   Reassociate an iterated Kronecker power
-- statement:
--   For every order-$d$ tensor $X$ and natural numbers $m$ and $r$, the iterated Kronecker power $(X^{\otimes m})^{\otimes r}$ is isomorphic to $X^{\otimes(rm)}$. Both restriction directions are retained, so the result can identify a repeatedly powered finite witness with its prescribed total exponent.
-- source:
--   Formal associativity of tensor powers; the identity is (x^m)^r=x^(mr) in the tensor isomorphism quotient used by Strassen asymptotic rank.

import Definitions.Def_mme_rank_bridge
open MME
universe u

theorem mme_kronPow_kronPow_isomorphic
    {K : Type u} [Field K] {d : ℕ}
    (X : TensorObj K d) (m r : ℕ) :
    TensorObj.Isomorphic
      ((X.kronPow m).kronPow r)
      (X.kronPow (r * m)) := by
  sorry
