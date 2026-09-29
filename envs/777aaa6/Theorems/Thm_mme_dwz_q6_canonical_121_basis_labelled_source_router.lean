-- Prove2me | Theorems.Thm_mme_dwz_q6_canonical_121_basis_labelled_source_router
-- name    : mme_dwz_q6_canonical_121_basis_labelled_source_router
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T09:53:08.432098+00:00
-- url     : https://prove2.me/theorems/2b8dbb34-f6ae-4a99-a49a-028a6d41f403
-- title:
--   Exact canonical q=6 basis router for the 121 component
-- statement:
--   The literal canonical q=6 Table-2 component 121 maps exactly to the twice-cyclically permuted coupled Coppersmith--Winograd constituent. The same maps send every named canonical Z-basis vector to the coordinate selected by the public grade-one decoder, retaining the split label needed for prescribed-word projection.
-- source:
--   Duan, Wu, and Zhou, arXiv:2210.10173v5, Section 6.3 and Table 2; Coppersmith--Winograd (1990), coupled constituent.

import Definitions.Def_mme_dwz_q6_grade_one_coord_data
import Definitions.Def_mme_permutation

open MME PiTensorProduct
open MME.DWZComponentRestriction

universe u

set_option autoImplicit false

theorem mme_dwz_q6_canonical_121_basis_labelled_source_router
    (K : Type u) [Field K] :
    ∃ maps : ∀ s : Fin 3,
        (cwSquareCanonicalGrading K 6).classOf s
            (cwSquareBlockType 1 2 1 s) →ₗ[K]
          (TensorObj.permObj (cyclicPerm.trans cyclicPerm)
            (coupledObj K 6)).V s,
      PiTensorProduct.map maps
          ((cwSquareCanonicalGrading K 6).blockTensor
            (cwSquareBlockType 1 2 1)) =
        (TensorObj.permObj (cyclicPerm.trans cyclicPerm)
          (coupledObj K 6)).t ∧
      ∀ p,
        maps 2 (canonicalComponentZBasis K (13 : Fin 15) p) =
          (Pi.single (dwzQ6GradeOneCoord p) 1 :
            (Fin 6 ⊕ Fin 6) → K) := by
  sorry
