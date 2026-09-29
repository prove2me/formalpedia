-- Prove2me | Theorems.Thm_mme_dwz_q6_canonical_211_basis_labelled_source_router
-- name    : mme_dwz_q6_canonical_211_basis_labelled_source_router
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T09:53:00.145091+00:00
-- url     : https://prove2.me/theorems/ddfa20ea-3167-4aa8-880f-a7c12403ff04
-- title:
--   Exact canonical q=6 basis router for the 211 component
-- statement:
--   The literal canonical q=6 Table-2 component 211 maps exactly to the once-cyclically permuted coupled Coppersmith--Winograd constituent. The same maps send every named canonical Z-basis vector to the coordinate selected by the public grade-one decoder, retaining the split label needed for prescribed-word projection.
-- source:
--   Duan, Wu, and Zhou, arXiv:2210.10173v5, Section 6.3 and Table 2; Coppersmith--Winograd (1990), coupled constituent.

import Definitions.Def_mme_dwz_q6_grade_one_coord_data
import Definitions.Def_mme_permutation

open MME PiTensorProduct
open MME.DWZComponentRestriction

universe u

set_option autoImplicit false

theorem mme_dwz_q6_canonical_211_basis_labelled_source_router
    (K : Type u) [Field K] :
    ∃ maps : ∀ s : Fin 3,
        (cwSquareCanonicalGrading K 6).classOf s
            (cwSquareBlockType 2 1 1 s) →ₗ[K]
          (TensorObj.permObj cyclicPerm (coupledObj K 6)).V s,
      PiTensorProduct.map maps
          ((cwSquareCanonicalGrading K 6).blockTensor
            (cwSquareBlockType 2 1 1)) =
        (TensorObj.permObj cyclicPerm (coupledObj K 6)).t ∧
      ∀ p,
        maps 2 (canonicalComponentZBasis K (14 : Fin 15) p) =
          (Pi.single (dwzQ6GradeOneCoord p) 1 :
            (Fin 6 ⊕ Fin 6) → K) := by
  sorry
