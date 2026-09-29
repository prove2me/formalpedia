-- Prove2me | Theorems.Thm_mme_dwz_q6_112_primary_hash_family_outer_restrict
-- name    : mme_dwz_q6_112_primary_hash_family_outer_restrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T08:33:16.742679+00:00
-- url     : https://prove2.me/theorems/c636da78-b5e4-41fd-988d-e68fbf92e06c
-- title:
--   Enhanced 112 primary-family outer extraction lands in the prescribed power
-- statement:
--   At the exact integral scale of the enhanced $112$ row, every primary asymmetric-hash family assembles into shared-third-mode stars whose direct sum is a restriction of the literal prescribed-histogram row-$112$ component power.  This theorem is the source-sensitive algebraic landing step: it retains the actual allowed-word projection and does not replace the source by an unrestricted coupled tensor power.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, enhanced 112 construction in Section 6.3 and Table 2; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_coupled_Ctensor_packaging_data
import Definitions.Def_mme_dwz_table2_standard_obj
import Definitions.Def_mme_dwz_q6_coupled_explicit_grading

open MME
open MME.DWZComponentRestriction

universe u

set_option autoImplicit false

theorem mme_dwz_q6_112_primary_hash_family_outer_restrict
    {K : Type u} [Field K] (m A H : ℕ)
    (family : CWQ6PrimaryHashFamily
      (50000000 * (20088623 * m))
      (21015 * (20088623 * m))
      (49978985 * (20088623 * m)) A H) :
    TensorObj.Restrict
      (TensorObj.bigAdd
        (CoupledCTensorPackaging.starObj
          (dwzQ6CoupledGrading K) family))
      (restrictedComponentPower K (12 : Fin 15) m) := by
  sorry
