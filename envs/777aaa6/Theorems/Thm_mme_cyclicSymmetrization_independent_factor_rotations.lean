-- Prove2me | Theorems.Thm_mme_cyclicSymmetrization_independent_factor_rotations
-- name    : mme_cyclicSymmetrization_independent_factor_rotations
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T04:52:59.548994+00:00
-- url     : https://prove2.me/theorems/0f6c2bcb-61e5-4338-9f18-701e594ba21b
-- title:
--   Independent cyclic rotations of Kronecker factors
-- statement:
--   For order-three tensors X and Y over any field, cyclic symmetrization of the Kronecker product of the cyclic rotation of X and the twice-cyclic rotation of Y is mutually restrictable with cyclic symmetrization of X tensor Y. The result follows by regrouping the six factors in the commutative tensor quotient.
-- source:
--   Tensor quotient permutation identities and tensor-product basis naturality.

import Definitions.Def_mme_cyclicSymmetrization_public_perm
import Definitions.Def_mme_rank_bridge

open MME
universe u
set_option autoImplicit false

theorem mme_cyclicSymmetrization_independent_factor_rotations
    {K : Type u} [Field K] (X Y : TensorObj K 3) :
    TensorObj.Isomorphic
      (cyclicSymmetrization (TensorObj.kron
        (TensorObj.permObj cyclicPerm X)
        (TensorObj.permObj (cyclicPerm.trans cyclicPerm) Y)))
      (cyclicSymmetrization (TensorObj.kron X Y)) := by sorry
