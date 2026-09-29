-- Prove2me | Theorems.Thm_mme_dwz_positive_224_original_profile_regional_restrict
-- name    : mme_dwz_positive_224_original_profile_regional_restrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-20T02:35:52.791983+00:00
-- url     : https://prove2.me/theorems/be9f17d7-4da5-41e5-b27b-b19c451b4b6d
-- title:
--   Claim 7.1 regional restriction for the original $T_{2,2,4}$ profile
-- statement:
--   Let $T_{2,2,4}$ be the canonical $(2,2,4)$ constituent of the fourth power of $CW_q$ over an arbitrary field, for every $q$. Using the exact object-158 data, the prescribed Z-split power of $T_{2,2,4}$ at the original parent profile restricts from the product of its three regional prescribed powers:
--
--   $$T^{\otimes D m}[\tilde\alpha] \;\trianglerighteq\; \bigotimes_{r=0}^{2} T^{\otimes D_r W_r m}[\tilde\alpha_r].$$
--
--   The theorem also records the exact identities that make this a genuine restriction with no rounding: the regional weights sum to $1000000000000000$, for every grade $a$ the parent count equals $\sum_r \text{count}_r(a)\,W_r$, and the parent length equals the sum of the regional lengths. This is DWZ Claim 7.1 for this component; it does not yet decompose the copies into square children or assert a value bound.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 7, Claim 7.1 and its proof, https://arxiv.org/html/2210.10173v5#S7. Exact object-158 data from mme_dwz_positive_224_regional_profile_data.

import Theorems.Thm_mme_dwz_prescribed_z_power_mixed_regional_restrict
import Definitions.Def_mme_dwz_positive_224_regional_profile_data
import Definitions.Def_mme_complete_split_cw_fourth_labels
import Mathlib.Tactic.FinCases

open MME MME.DWZComponentRestriction MME.DWZRestrictedValue
  MME.CompleteSplit.CWFourth MME.StothersFourth MME.DWZPositiveComponent224
  Module BigOperators
open scoped Classical
universe u
set_option autoImplicit false

theorem mme_dwz_positive_224_original_profile_regional_restrict
    {K : Type u} [Field K] (q m : ℕ) :
    (∑ r, regionalWeight r = 1000000000000000) ∧
    (∀ a : Fin 5, parentProfile.count a =
      ∑ r, (regionalProfile r).count a * regionalWeight r) ∧
    parentProfile.length m =
      ∑ r, (regionalProfile r).length (regionalWeight r * m) ∧
    TensorObj.Restrict
      (TensorObj.kronFin 3 (fun r ↦ prescribedZPower
        (cwFourthConstituent K q 2 2 4)
        (constituentBasis K q 2 2 4 2)
        (fun a : LiftedCoarseCoordinate.{u} q 4 ↦ cwSquarePairGrade q a.down.val.1)
        (regionalProfile r) (regionalWeight r * m)))
      (prescribedZPower
        (cwFourthConstituent K q 2 2 4)
        (constituentBasis K q 2 2 4 2)
        (fun a : LiftedCoarseCoordinate.{u} q 4 ↦ cwSquarePairGrade q a.down.val.1)
        parentProfile m) := by sorry
