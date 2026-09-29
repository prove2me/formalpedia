-- Prove2me | solution 1 for mme_CW_square_canonical_elementary_blocks
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T21:41:30.477319+00:00
-- url     : https://prove2.me/submissions/7363221c-c199-4f33-9468-3af3d779c2b3

import Theorems.Thm_mme_CW_square_canonical_support_and_scalar_blocks
import Theorems.Thm_mme_CW_square_canonical_rect013_031
import Theorems.Thm_mme_CW_square_canonical_rect103_301
import Theorems.Thm_mme_CW_square_canonical_rect130_310
import Theorems.Thm_mme_CW_square_canonical_central022_restrict
import Theorems.Thm_mme_CW_square_canonical_central202_restrict
import Theorems.Thm_mme_CW_square_canonical_central220_restrict

open MME

universe u

set_option autoImplicit false

theorem solution
    {K : Type u} [Field K] (q : ℕ) :
    (∀ I J L : Fin 5, I.val + J.val + L.val ≠ 4 →
      (cwSquareCanonicalGrading K q).blockTensor
        (cwSquareBlockType I J L) = 0) ∧
    TensorObj.Restrict (MMObj K 1 1 1)
      ((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType 0 0 4)) ∧
    TensorObj.Restrict (MMObj K 1 1 1)
      ((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType 0 4 0)) ∧
    TensorObj.Restrict (MMObj K 1 1 1)
      ((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType 4 0 0)) ∧
    TensorObj.Restrict (MMObj K 1 1 (2 * q))
      ((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType 0 1 3)) ∧
    TensorObj.Restrict (MMObj K 1 1 (2 * q))
      ((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType 0 3 1)) ∧
    TensorObj.Restrict (MMObj K (2 * q) 1 1)
      ((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType 1 0 3)) ∧
    TensorObj.Restrict (MMObj K (2 * q) 1 1)
      ((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType 3 0 1)) ∧
    TensorObj.Restrict (MMObj K 1 (2 * q) 1)
      ((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType 1 3 0)) ∧
    TensorObj.Restrict (MMObj K 1 (2 * q) 1)
      ((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType 3 1 0)) ∧
    TensorObj.Restrict (MMObj K 1 1 (q ^ 2 + 2))
      ((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType 0 2 2)) ∧
    TensorObj.Restrict (MMObj K (q ^ 2 + 2) 1 1)
      ((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType 2 0 2)) ∧
    TensorObj.Restrict (MMObj K 1 (q ^ 2 + 2) 1)
      ((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType 2 2 0)) := by
  rcases mme_CW_square_canonical_support_and_scalar_blocks (K := K) q with
    ⟨hSupport, h004, h040, h400⟩
  rcases mme_CW_square_canonical_rect013_031 (K := K) q with ⟨h013, h031⟩
  rcases mme_CW_square_canonical_rect103_301 (K := K) q with ⟨h103, h301⟩
  rcases mme_CW_square_canonical_rect130_310 (K := K) q with ⟨h130, h310⟩
  exact ⟨hSupport, h004, h040, h400, h013, h031, h103, h301, h130, h310,
    mme_CW_square_canonical_central022_restrict (K := K) q,
    mme_CW_square_canonical_central202_restrict (K := K) q,
    mme_CW_square_canonical_central220_restrict (K := K) q⟩
