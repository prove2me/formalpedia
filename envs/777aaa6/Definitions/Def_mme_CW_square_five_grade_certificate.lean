-- Prove2me | Definitions.Def_mme_CW_square_five_grade_certificate
-- name    : mme_CW_square_five_grade_certificate
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-24T15:54:25.557944+00:00
-- url     : https://prove2.me/theorems/76c0eade-4063-4937-b888-dee275db9d38
-- title:
--   Algebraic five-grade orbit certificate for the square of the CW tensor
-- statement:
--   For the tensor square $T_q \otimes T_q$, this module packages a five-grade decomposition whose supported grade triples satisfy $I+J+K=4$. It records concrete restrictions for the four orbit shapes displayed in equation (11): the scalar $(0,0,4)$ orbit; the six $\langle1,1,2q\rangle$ blocks in the $(0,1,3)$ orbit; the three $\langle1,1,q^2+2\rangle$ blocks in the $(0,2,2)$ orbit; and the explicit coupled $(1,1,2)$ tensor together with its two cyclic rotations. The aggregate coupled field identifies the three rotated blocks with the cyclic symmetrization used in the value argument. This keeps the algebraic block identification separate from subsequent hashing and asymptotic counting.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), regrouped tensor-square construction (11) and constituent cases (a)--(d) on journal pp. 265--266; coupled constituent and cyclic value lemma on pp. 270--272.

import Definitions.Def_mme_block_subtensor
import Definitions.Def_mme_CW_coupled_value
import Definitions.Def_mme_CW_tensor
import Definitions.Def_mme_tensor_rank

/-!
# Algebraic five-grade certificate for the square of the CW tensor

This structure records the algebraic input to Section 8 separately from the
subsequent multinomial and Salem--Spencer argument.  The fifteen supported
five-grade blocks are grouped into the four cyclic orbit shapes displayed on
CW90 journal pp. 265--266.
-/

namespace MME

universe u

/-- The order-three block type with grades `(I,J,K)`. -/
def cwSquareBlockType (I J K : Fin 5) : Fin 3 → Fin 5
  | ⟨0, _⟩ => I
  | ⟨1, _⟩ => J
  | ⟨2, _⟩ => K

/-- A certificate identifying every orbit of the five-grading of
`T_q ⊗ T_q`.  Restriction is stated in the direction needed by the laser
method: each displayed constituent is obtained from its graded block. -/
structure CWSquareFiveGradeCertificate
    (K : Type u) [Field K] (q : ℕ) where
  grading : (TensorObj.kron (CWObj K q) (CWObj K q)).TypeGrading 5
  support : ∀ I J L : Fin 5,
    I.val + J.val + L.val ≠ 4 →
      grading.blockTensor (cwSquareBlockType I J L) = 0

  scalar004 : TensorObj.Restrict (MMObj K 1 1 1)
    (grading.blockSubtensor (cwSquareBlockType 0 0 4))
  scalar040 : TensorObj.Restrict (MMObj K 1 1 1)
    (grading.blockSubtensor (cwSquareBlockType 0 4 0))
  scalar400 : TensorObj.Restrict (MMObj K 1 1 1)
    (grading.blockSubtensor (cwSquareBlockType 4 0 0))

  rect013 : TensorObj.Restrict (MMObj K 1 1 (2 * q))
    (grading.blockSubtensor (cwSquareBlockType 0 1 3))
  rect031 : TensorObj.Restrict (MMObj K 1 1 (2 * q))
    (grading.blockSubtensor (cwSquareBlockType 0 3 1))
  rect103 : TensorObj.Restrict (MMObj K (2 * q) 1 1)
    (grading.blockSubtensor (cwSquareBlockType 1 0 3))
  rect301 : TensorObj.Restrict (MMObj K (2 * q) 1 1)
    (grading.blockSubtensor (cwSquareBlockType 3 0 1))
  rect130 : TensorObj.Restrict (MMObj K 1 (2 * q) 1)
    (grading.blockSubtensor (cwSquareBlockType 1 3 0))
  rect310 : TensorObj.Restrict (MMObj K 1 (2 * q) 1)
    (grading.blockSubtensor (cwSquareBlockType 3 1 0))

  central022 : TensorObj.Restrict (MMObj K 1 1 (q ^ 2 + 2))
    (grading.blockSubtensor (cwSquareBlockType 0 2 2))
  central202 : TensorObj.Restrict (MMObj K (q ^ 2 + 2) 1 1)
    (grading.blockSubtensor (cwSquareBlockType 2 0 2))
  central220 : TensorObj.Restrict (MMObj K 1 (q ^ 2 + 2) 1)
    (grading.blockSubtensor (cwSquareBlockType 2 2 0))

  coupled112 : TensorObj.Restrict (coupledObj K q)
    (grading.blockSubtensor (cwSquareBlockType 1 1 2))
  coupledCyclic :
    TensorObj.Restrict
      (cyclicSymmetrization (coupledObj K q))
      (TensorObj.kron
        (grading.blockSubtensor (cwSquareBlockType 1 1 2))
        (TensorObj.kron
          (grading.blockSubtensor (cwSquareBlockType 2 1 1))
          (grading.blockSubtensor (cwSquareBlockType 1 2 1))))

end MME


