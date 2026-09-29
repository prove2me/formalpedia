-- Prove2me | Theorems.Thm_mme_dwz_q6_112_restricted_primary_star_assembly
-- name    : mme_dwz_q6_112_restricted_primary_star_assembly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T07:45:59.524833+00:00
-- url     : https://prove2.me/theorems/de7477c1-7ed2-464d-a3a1-68aad492e160
-- title:
--   Shared-Z primary stars land in the prescribed q=6 row-112 power
-- statement:
--   At the exact integer scale of the enhanced $112$ row in the $q=6$ Table-2 distribution, every induced primary hash family assembles into $A$ shared-Z C-tensor stars. Their direct sum is a restriction of the literal prescribed-histogram row-112 component power. Each star has the standard $\langle 1,H,1\rangle$ support, and its component indexed by $h$ is isomorphic to the exact coupled graded-address block specified by the hash-family entry $(a,h)$. This is the source-sensitive landing statement: it records the common third-mode extraction and the allowed-word projection before any numerical matrix-multiplication volume calculation.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, enhanced 112 construction in Section 6.3 and Table 2; https://arxiv.org/abs/2210.10173

import Definitions.Def_CTensorOneHOneCertificate
import Definitions.Def_mme_CW_q6_primary_hash_family
import Definitions.Def_mme_dwz_table2_standard_obj
import Definitions.Def_mme_dwz_q6_coupled_explicit_grading
import Definitions.Def_mme_induced_word_zeroing

open MME
open MME.DWZComponentRestriction

universe u

set_option autoImplicit false

theorem mme_dwz_q6_112_restricted_primary_star_assembly
    {K : Type u} [Field K] (m A H : ℕ)
    (family : CWQ6PrimaryHashFamily
      (50000000 * (20088623 * m))
      (21015 * (20088623 * m))
      (49978985 * (20088623 * m)) A H) :
    ∃ star : Fin A → TensorObj K 3,
      TensorObj.Restrict (TensorObj.bigAdd star)
        (restrictedComponentPower K (12 : Fin 15) m) ∧
      ∀ a : Fin A,
        ∃ starGrading : (star a).TypeGrading (H + 1),
          (∀ σ : Fin 3 → Fin (H + 1),
            σ ∉ Finset.univ.image (cTensorOneHOneAddress H) →
              starGrading.blockTensor σ = 0) ∧
          ∀ h : Fin H,
            TensorObj.Isomorphic
              (gradedAddressBlock (dwzQ6CoupledGrading K)
                (family.entry (a, h)).1)
              (starGrading.blockSubtensor
                (cTensorOneHOneAddress H h)) := by
  sorry
