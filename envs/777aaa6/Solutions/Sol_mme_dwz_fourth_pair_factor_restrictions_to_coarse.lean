-- Prove2me | solution 1 for mme_dwz_fourth_pair_factor_restrictions_to_coarse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-05T15:22:08.576703+00:00
-- url     : https://prove2.me/submissions/d6fac54d-a20d-448b-a0f0-f1a07d5b9bb1

import Definitions.Def_mme_dwz_square_data
import Theorems.Thm_mme_CW_fourth_fine_block_restrict_of_factors
import Theorems.Thm_mme_CW_fourth_fine_block_restrict_coarse_block

open MME

universe u

set_option autoImplicit false
set_option warningAsError true

/-- Compose the proved factorwise fine restriction with its literal coarse
block inclusion; no tensor expansion or component value is reproved. -/
theorem solution
    {K : Type u} [Field K] (q : ℕ) (p : Fin 15 × Fin 15)
    (sigma : Fin 3 → Fin 9)
    (hx : (DWZSquare.shapeX p.1).val + (DWZSquare.shapeX p.2).val =
      (sigma 0).val)
    (hy : (DWZSquare.shapeY p.1).val + (DWZSquare.shapeY p.2).val =
      (sigma 1).val)
    (hz : (DWZSquare.shapeZ p.1).val + (DWZSquare.shapeZ p.2).val =
      (sigma 2).val)
    {X Y : TensorObj K 3}
    (hX : TensorObj.Restrict X
      ((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType
          (DWZSquare.shapeX p.1) (DWZSquare.shapeY p.1) (DWZSquare.shapeZ p.1))))
    (hY : TensorObj.Restrict Y
      ((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType
          (DWZSquare.shapeX p.2) (DWZSquare.shapeY p.2) (DWZSquare.shapeZ p.2)))) :
    TensorObj.Restrict (TensorObj.kron X Y)
      ((MME.StothersFourth.cwFourthCanonicalGrading K q).blockSubtensor sigma) := by
  apply TensorObj.Restrict.trans
    (mme_CW_fourth_fine_block_restrict_of_factors q
      (DWZSquare.shapeX p.1) (DWZSquare.shapeY p.1) (DWZSquare.shapeZ p.1)
      (DWZSquare.shapeX p.2) (DWZSquare.shapeY p.2) (DWZSquare.shapeZ p.2) hX hY)
  apply mme_CW_fourth_fine_block_restrict_coarse_block q
    (DWZSquare.shapeX p.1) (DWZSquare.shapeY p.1) (DWZSquare.shapeZ p.1)
    (DWZSquare.shapeX p.2) (DWZSquare.shapeY p.2) (DWZSquare.shapeZ p.2) sigma
  intro s
  fin_cases s
  · exact hx
  · exact hy
  · exact hz
