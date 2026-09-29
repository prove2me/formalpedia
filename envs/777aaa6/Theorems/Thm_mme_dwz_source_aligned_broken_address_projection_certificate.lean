-- Prove2me | Theorems.Thm_mme_dwz_source_aligned_broken_address_projection_certificate
-- name    : mme_dwz_source_aligned_broken_address_projection_certificate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T13:48:53.234612+00:00
-- url     : https://prove2.me/theorems/adbb5d7e-7b07-44d8-98c3-2bb9e0dfd93c
-- title:
--   The source-aligned broken copy is an exact Z-only restriction of its retained coarse address
-- statement:
--   For a retained Table-2 outer word, project the canonical $Z$-basis of its coarse source address onto precisely the useful words whose literal labels are nonholes. The resulting source-aligned broken tensor is a genuine restriction of the coarse address. Its selected $X$ and $Y$ spaces remain complete, and its selected $Z$ space is exactly
--
--   $$
--   \operatorname{span}\{b_W: W\text{ carries a useful nonhole label}\}.
--   $$
--
--   Thus the broken copy is modeled by one $Z$-only projection and preserves the shared $X/Y$ variables required by the DWZ standard form; it is not a direct sum of singleton fine-address tensors.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Remark 5.1, Definitions 5.2--5.5, and Additional Zeroing-Out Step 2; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_source_aligned_broken_obj
import Theorems.Thm_mme_basisZAllowedSubtensor_projection_certificate

open MME Module

universe u

open MME.DWZSourceAligned

set_option autoImplicit false

theorem mme_dwz_source_aligned_broken_address_projection_certificate
    (K : Type u) [Field K]
    (m : ℕ) {N : ℕ} (outer : Fin N → Fin 15)
    (copy : DWZSquare.BrokenBlockCopy
      (DWZTable2StandardForm.UsefulBlock m outer)) :
    TensorObj.Restrict (brokenAddressObj K m outer copy)
        (coarseAddressObj K outer) ∧
      (brokenAddressGrading K m outer copy).classOf 0 0 = ⊤ ∧
      (brokenAddressGrading K m outer copy).classOf 1 0 = ⊤ ∧
      (brokenAddressGrading K m outer copy).classOf 2 0 =
        Submodule.span K
          (coarseAddressZBasis K outer ''
            {W | addressWordSurvives m outer copy W}) := by
  sorry
