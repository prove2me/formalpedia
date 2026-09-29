-- Prove2me | Theorems.Thm_mme_bigAdd_cartesian_kron_isomorphic
-- name    : mme_bigAdd_cartesian_kron_isomorphic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T12:29:11.7135+00:00
-- url     : https://prove2.me/theorems/fe173578-450f-490b-85f8-6cb6dd9b48f0
-- title:
--   Cartesian Kronecker product of two tensor direct sums
-- statement:
--   The direct sum of all A·B pairwise Kronecker products X_a tensor Y_b is isomorphic to the Kronecker product of the direct sum of the X_a with the direct sum of the Y_b. This is the full Cartesian distributor needed to combine two independently extracted outer tensor families without identifying their labels or losing off-diagonal pairs.
-- source:
--   Standard distributivity of Kronecker product over finite direct sums in the tensor isomorphism quotient; used here for independent C-tensor half-family assembly in the DWZ square analysis.

import Definitions.Def_mme_rank_bridge

open MME BigOperators

universe u

set_option autoImplicit false

theorem mme_bigAdd_cartesian_kron_isomorphic
    {K : Type u} [Field K] {d A B : ℕ}
    (X : Fin A → TensorObj K d) (Y : Fin B → TensorObj K d) :
    TensorObj.Isomorphic
      (TensorObj.bigAdd (fun r : Fin (A * B) ↦
        TensorObj.kron
          (X (finProdFinEquiv.symm r).1)
          (Y (finProdFinEquiv.symm r).2)))
      (TensorObj.kron (TensorObj.bigAdd X) (TensorObj.bigAdd Y)) := by
  sorry
