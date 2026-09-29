-- Prove2me | Theorems.Thm_mme_dwz_positive_152_original_profile_regional_restrict
-- name    : mme_dwz_positive_152_original_profile_regional_restrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-20T02:07:41.854993+00:00
-- url     : https://prove2.me/theorems/5a4f0183-5170-4f0f-8695-881c185eaeda
-- title:
--   Claim 7.1 regional restriction for the original $T_{1,5,2}$ profile
-- statement:
--   Let $T_{1,5,2}$ be the canonical $(1,5,2)$ constituent of the fourth power of $CW_q$ over an arbitrary field, for every $q$. Using the exact object-153 data, the prescribed Z-split power of $T_{1,5,2}$ at the original parent profile restricts from the product of its three regional prescribed powers:
--
--   $$T^{\otimes D m}[\tilde\alpha] \;\trianglerighteq\; \bigotimes_{r=0}^{2} T^{\otimes D_r W_r m}[\tilde\alpha_r].$$
--
--   The theorem also records the exact identities that make this a genuine restriction with no rounding: the regional weights sum to $999999999999999$, for every grade $a$ the parent count equals $\sum_r \text{count}_r(a)\,W_r$, and the parent length equals the sum of the regional lengths. This is DWZ Claim 7.1 for this component; it does not yet decompose the copies into square children or assert a value bound.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 7, Claim 7.1 and its proof, https://arxiv.org/html/2210.10173v5#S7. Exact object-153 data from mme_dwz_positive_152_regional_profile_data.

import Theorems.Thm_mme_dwz_prescribed_z_power_mixed_regional_restrict
import Definitions.Def_mme_dwz_positive_152_regional_profile_data
import Definitions.Def_mme_complete_split_cw_fourth_labels
import Mathlib.Tactic.FinCases

open MME MME.DWZComponentRestriction MME.DWZRestrictedValue
  MME.CompleteSplit.CWFourth MME.StothersFourth MME.DWZPositiveComponent152
  Module BigOperators
open scoped Classical
universe u
set_option autoImplicit false

theorem mme_dwz_positive_152_original_profile_regional_restrict
    {K : Type u} [Field K] (q m : ℕ) :
    (∑ r, regionalWeight r = 999999999999999) ∧
    (∀ a : Fin 5, parentProfile.count a =
      ∑ r, (regionalProfile r).count a * regionalWeight r) ∧
    parentProfile.length m =
      ∑ r, (regionalProfile r).length (regionalWeight r * m) ∧
    TensorObj.Restrict
      (TensorObj.kronFin 3 (fun r ↦ prescribedZPower
        (cwFourthConstituent K q 1 5 2)
        (constituentBasis K q 1 5 2 2)
        (fun a : LiftedCoarseCoordinate.{u} q 2 ↦ cwSquarePairGrade q a.down.val.1)
        (regionalProfile r) (regionalWeight r * m)))
      (prescribedZPower
        (cwFourthConstituent K q 1 5 2)
        (constituentBasis K q 1 5 2 2)
        (fun a : LiftedCoarseCoordinate.{u} q 2 ↦ cwSquarePairGrade q a.down.val.1)
        parentProfile m) := by sorry
