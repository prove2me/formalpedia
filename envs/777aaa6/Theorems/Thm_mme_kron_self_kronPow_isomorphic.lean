-- Prove2me | Theorems.Thm_mme_kron_self_kronPow_isomorphic
-- name    : mme_kron_self_kronPow_isomorphic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T04:44:19.051493+00:00
-- url     : https://prove2.me/theorems/8d12c5c7-674d-495d-be3b-0ab1f0fdcf6e
-- title:
--   A power of a Kronecker square is the corresponding even tensor power
-- statement:
--   Let $X$ be an order-$d$ tensor over a field $K$. For every natural number $N$, the $N$-fold Kronecker power of the square $X\otimes X$ is isomorphic, in the tensor-restriction sense, to the $2N$-fold Kronecker power of $X$:
--
--   $$
--   (X\otimes X)^{\otimes N} \cong X^{\otimes 2N}.
--   $$
--
--   Here isomorphism means that each tensor restricts to the other by modewise linear maps. This reassociation lemma lets tensor-square laser constructions reuse block restrictions formulated for an even power of the original tensor.
--
--   **Formalization Note** The proof passes to the isomorphism quotient `TensorQ`, where Kronecker product and Kronecker power are multiplication and natural power in a commutative semiring.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), Construction (11) and its N-th tensor power on journal pp. 265–267; https://www.sciencedirect.com/science/article/pii/S0747717108800132

import Definitions.Def_mme_rank_bridge
open MME
universe u

theorem mme_kron_self_kronPow_isomorphic
    {K : Type u} [Field K] {d : ℕ} (X : TensorObj K d) (N : ℕ) :
    TensorObj.Isomorphic
      ((TensorObj.kron X X).kronPow N)
      (X.kronPow (2 * N)) := by sorry
