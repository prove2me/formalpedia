-- Prove2me | Theorems.Thm_mme_cyclic_triple_grading_block_subtensor_iso
-- name    : mme_cyclic_triple_grading_block_subtensor_iso
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T23:28:49.198639+00:00
-- url     : https://prove2.me/theorems/ddc02461-0077-429f-8e91-1deecd616e55
-- title:
--   Blocks of the cyclic product grading factor into three cyclic blocks
-- statement:
--   Let $G$ grade a three-mode tensor $T$. A block of the induced grading on the cyclic symmetrization $T\otimes\pi T\otimes\pi^2T$ is canonically isomorphic to the Kronecker product of the corresponding block of $T$ and the two appropriately mode-permuted blocks:
--
--   $$
--   B_{\mathrm{cyc}}(\rho_X,\rho_Y,\rho_Z)
--   \cong B_G(\rho_X)\otimes\pi B_G(\rho_Y)\otimes\pi^2 B_G(\rho_Z).
--   $$
--
--   The inverse cyclic permutations in the grade labels ensure that every factor is read in its original mode order. This theorem is the tensor-algebra bridge used to attach component restrictions and values to each edge retained by cyclic hashing.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), cyclic product and component extraction in Lemma 5.1, pp. 365--367; https://www.maths.ed.ac.uk/~sandy/a11164.pdf. The block factorization is the standard product-grading identity.

import Definitions.Def_mme_cyclic_triple_grading
import Theorems.Thm_mme_TypeGrading_kron_blockSubtensor_iso

open MME TensorObj.TypeGrading

universe u

set_option autoImplicit false

theorem mme_cyclic_triple_grading_block_subtensor_iso
    {K : Type u} [Field K] {T : TensorObj K 3} {t : Nat}
    (G : T.TypeGrading t)
    (rhoX rhoY rhoZ : Fin 3 -> Fin t) :
    TensorObj.Isomorphic
      (TensorObj.kron (G.blockSubtensor rhoX)
        (TensorObj.kron
          ((permObjGrading G cyclicPerm).blockSubtensor
            (fun i => rhoY (cyclicPerm.symm i)))
          ((permObjGrading G (cyclicPerm.trans cyclicPerm)).blockSubtensor
            (fun i => rhoZ ((cyclicPerm.trans cyclicPerm).symm i)))))
      ((mmeCyclicTripleGrading G).blockSubtensor
        (mmeCyclicTripleGrade rhoX rhoY rhoZ)) := by
  sorry
