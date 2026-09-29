-- Prove2me | Theorems.Thm_mme_dwz_q6_canonical_121_211_basis_labelled_source_routers
-- name    : mme_dwz_q6_canonical_121_211_basis_labelled_source_routers
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T09:21:44.125117+00:00
-- url     : https://prove2.me/theorems/203b79b2-3bca-46df-94b1-9e209e702793
-- title:
--   Exact basis-labelled q=6 routers for Table-2 rows 121 and 211
-- statement:
--   There is one explicit decoder from the canonical q=6 coarse-grade-one Z basis to the two six-element fine-coordinate families.  It sends the left family to split grade 0 and the right family to split grade 1.  The literal canonical Table-2 block 121 maps to the twice-cyclically permuted coupled constituent, and block 211 maps to the once-cyclically permuted coupled constituent.  Both maps preserve the tensor exactly and send every named canonical Z-basis vector to the corresponding coordinate vector under the same decoder.  This is the source-basis interface needed to pair the two duplicated orientations in full six-symmetrization while retaining the prescribed Table-2 split projector.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Table 2 and the cyclic 121/211 analysis in Section 6.3; Coppersmith and Winograd, Journal of Symbolic Computation 9 (1990), coupled constituent pp. 266 and 270.

import Mathlib.Data.Fin.VecNotation
import Definitions.Def_mme_CW_square_canonical_grading
import Definitions.Def_mme_permutation
import Definitions.Def_mme_dwz_component_word_projection

open MME PiTensorProduct
open MME.DWZComponentRestriction

universe u

set_option autoImplicit false

theorem mme_dwz_q6_canonical_121_211_basis_labelled_source_routers
    (K : Type u) [Field K] :
    ∃ coord : LiftedCoarsePair.{u} 6 1 ≃ (Fin 6 ⊕ Fin 6),
      (∀ p,
        p.leftGrade =
          Sum.elim (fun _ : Fin 6 ↦ (0 : Fin 3))
            (fun _ : Fin 6 ↦ (1 : Fin 3)) (coord p)) ∧
      (∃ maps : ∀ s : Fin 3,
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
            (Pi.single (coord p) 1 : (Fin 6 ⊕ Fin 6) → K)) ∧
      (∃ maps : ∀ s : Fin 3,
          (cwSquareCanonicalGrading K 6).classOf s
              (cwSquareBlockType 2 1 1 s) →ₗ[K]
            (TensorObj.permObj cyclicPerm (coupledObj K 6)).V s,
        PiTensorProduct.map maps
            ((cwSquareCanonicalGrading K 6).blockTensor
              (cwSquareBlockType 2 1 1)) =
          (TensorObj.permObj cyclicPerm (coupledObj K 6)).t ∧
        ∀ p,
          maps 2 (canonicalComponentZBasis K (14 : Fin 15) p) =
            (Pi.single (coord p) 1 : (Fin 6 ⊕ Fin 6) → K)) := by
  sorry
