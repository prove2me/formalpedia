-- Prove2me | Theorems.Thm_mme_dwz_positive_161_original_profile_regional_restrict
-- name    : mme_dwz_positive_161_original_profile_regional_restrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-19T16:33:09.305742+00:00
-- url     : https://prove2.me/theorems/6043ba82-b208-4bc3-b088-5a8610dd1262
-- title:
--   Claim 7.1 regional restriction for the original {1,6,1}$ profile
-- statement:
--   Let $T_{1,6,1}$ be the canonical $(1,6,1)$ constituent of the fourth power of $CW_q$ over an arbitrary field, for every $q$. Using the exact object-154 data, the prescribed Z-split power of $T_{1,6,1}$ at the original parent profile restricts from the product of its three regional prescribed powers:
--
--   $$T_{1,6,1}^{\otimes D m}[\tilde\alpha] \;\trianglerighteq\; \bigotimes_{r=0}^{2} T_{1,6,1}^{\otimes D_r W_r m}[\tilde\alpha_r].$$
--
--   The theorem also records the three exact identities that make this a genuine restriction with no rounding: the regional weights sum to $10^{15}$; for every grade $a$ the parent count equals $\sum_r \text{count}_r(a)\,W_r$; and the parent length equals the sum of the regional lengths. Region 1 has weight zero, so its factor has length zero.
--
--   This is DWZ Claim 7.1 for this component. It keeps copies of the same parent constituent; it does not yet decompose them into square children or assert a value bound.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 7, Claim 7.1 and its proof (regional zeroing of Z-blocks), https://arxiv.org/html/2210.10173v5#S7. Exact object-154 data from mme_dwz_positive_161_regional_profile_data.

import Theorems.Thm_mme_dwz_prescribed_z_power_mixed_regional_restrict
import Definitions.Def_mme_dwz_positive_161_regional_profile_data
import Definitions.Def_mme_complete_split_cw_fourth_labels
import Mathlib.Tactic.FinCases

open MME MME.DWZComponentRestriction MME.DWZRestrictedValue
  MME.CompleteSplit.CWFourth MME.StothersFourth MME.DWZPositiveComponent161
  Module BigOperators
open scoped Classical
universe u
set_option autoImplicit false

theorem mme_dwz_positive_161_original_profile_regional_restrict
    {K : Type u} [Field K] (q m : ℕ) :
    (∑ r, regionalWeight r = 1000000000000000) ∧
    (∀ a : Fin 5, parentProfile.count a =
      ∑ r, (regionalProfile r).count a * regionalWeight r) ∧
    parentProfile.length m =
      ∑ r, (regionalProfile r).length (regionalWeight r * m) ∧
    TensorObj.Restrict
      (TensorObj.kronFin 3 (fun r ↦ prescribedZPower
        (cwFourthConstituent K q 1 6 1)
        (constituentBasis K q 1 6 1 2)
        (fun a : LiftedCoarseCoordinate.{u} q 1 ↦ cwSquarePairGrade q a.down.val.1)
        (regionalProfile r) (regionalWeight r * m)))
      (prescribedZPower
        (cwFourthConstituent K q 1 6 1)
        (constituentBasis K q 1 6 1 2)
        (fun a : LiftedCoarseCoordinate.{u} q 1 ↦ cwSquarePairGrade q a.down.val.1)
        parentProfile m) := by sorry
