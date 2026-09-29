-- Prove2me | Theorems.Thm_mme_diagObj_kron_isomorphic_bigAdd_const
-- name    : mme_diagObj_kron_isomorphic_bigAdd_const
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T17:25:04.688343+00:00
-- url     : https://prove2.me/theorems/48264c8d-b583-4cae-bee1-63e642537a65
-- title:
--   A diagonal tensor times $S$ is a direct sum of copies of $S$
-- statement:
--   Let $S$ be an order-$d$ tensor over a field $K$. Multiplying $S$ by the size-$n$ diagonal tensor is tensor-isomorphic to taking the direct sum of $n$ copies of $S$:
--
--   $$
--   \langle n\rangle\otimes S\;\cong\;\bigoplus_{j=1}^{n} S.
--   $$
--
--   This identity is the tensor-algebra bridge between an induced matching, naturally expressed as a direct sum of retained blocks, and the canonical diagonal grading used in laser-method certificates.
-- source:
--   Standard distributivity of tensor product over finite direct sums; formalized by the commutative-semiring laws for TensorQ in Definitions.Def_mme_tensor_quotient and the descent identities in Definitions.Def_mme_rank_bridge.

import Definitions.Def_mme_rank_bridge
open MME BigOperators
universe u

theorem mme_diagObj_kron_isomorphic_bigAdd_const
    {K : Type u} [Field K] {d : ℕ}
    (S : TensorObj K d) (n : ℕ) :
    TensorObj.Isomorphic
      (TensorObj.kron (TensorObj.diagObj K d n) S)
      (TensorObj.bigAdd (fun _ : Fin n => S)) := by
  sorry
