-- Prove2me | Theorems.Thm_mme_dwz_broken_standard_obj_projection_certificate
-- name    : mme_dwz_broken_standard_obj_projection_certificate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T09:20:11.442479+00:00
-- url     : https://prove2.me/theorems/502896d3-eb1c-482a-8f3d-4b111ba12002
-- title:
--   The literal broken standard tensor is an exact Z-only restriction
-- statement:
--   Fix a field $K$, an integral scale $m\geq0$, and a broken Table-2 standard-form copy $C$. Let $T^*(m)$ be the complete standard tensor and $T_C^*(m)$ its literal nonhole mask. Then
--
--   $$
--   T_C^*(m)\preceq T^*(m)
--   $$
--
--   by a genuine modewise tensor restriction. The selected $X$ and $Y$ mode spaces are the full corresponding spaces of $T^*(m)$. If $b_W$ denotes the canonical grouped $Z$-basis vector indexed by an available component-word family $W$, and $\ell(W)$ is its literal useful fine-block label, then the selected $Z$ mode is exactly
--
--   $$
--   \operatorname{span}\left\{ b_W : \ell(W)\in\operatorname{nonholes}(C) \right\}.
--   $$
--
--   Thus the restriction deletes exactly the small $Z$ blocks marked as holes and neither splits nor duplicates the shared $X/Y$ spaces. The statement includes zero scale and an empty nonhole set.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definitions 5.2--5.5 and Definition 6.3, PDF pp. 47--49 / printed pp. 46--48, specialized to Section 6.3/Table 2; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_broken_standard_obj
import Theorems.Thm_mme_basisZAllowedSubtensor_projection_certificate

open MME Module
open MME.DWZComponentRestriction

universe u

set_option autoImplicit false

theorem mme_dwz_broken_standard_obj_projection_certificate
    {K : Type u} [Field K] (m : ℕ)
    (copy : MME.DWZSquare.BrokenBlockCopy
      (MME.DWZTable2StandardForm.UsefulBlock m
        (groupedOuter (m := m)))) :
    TensorObj.Restrict
        (dwzBrokenStandardObj K m copy)
        (dwzTable2StandardObj K m) ∧
      (dwzBrokenStandardGrading K m copy).classOf 0 0 = ⊤ ∧
      (dwzBrokenStandardGrading K m copy).classOf 1 0 = ⊤ ∧
      (dwzBrokenStandardGrading K m copy).classOf 2 0 =
        Submodule.span K
          (dwzTable2StandardZBasis K m ''
            {W | groupedUsefulBlock m W ∈ copy.nonholes}) := by
  sorry
