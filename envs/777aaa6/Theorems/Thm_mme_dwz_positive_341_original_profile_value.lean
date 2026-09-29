-- Prove2me | Theorems.Thm_mme_dwz_positive_341_original_profile_value
-- name    : mme_dwz_positive_341_original_profile_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-21T16:59:13.977717+00:00
-- url     : https://prove2.me/theorems/c84f4847-5e7c-442d-9f50-8d5d883f084e
-- title:
--   Positive fourth component T_{3,4,1}: original-profile value at the ledger rate
-- statement:
--   Let $T_{3,4,1}$ be the actual canonical $(3,4,1)$ constituent of the fourth power of the Coppersmith–Winograd tensor $CW_5$, over an arbitrary field. Retain the original rational prescribed Z-split profile of released object 167. Its Z-coordinate is $k = 1$, so the profile records the left grade, with denominator $D = 1000000000000000000000000000000$ and count vector
--
--   $$(500000000007580549944575306560,\ 499999999992419450055424693440,\ 0,\ 0,\ 0).$$
--
--   At $	au = 790643/1000000$, the restriction-based six-symmetrized value certificate for this exact profile is at least
--
--   $$\exp\!\left(rac{6159531789539}{1000000000000}ight).$$
--
--   Explicitly, every positive strict lower base has actual finite direct sums of matrix-multiplication tensors restricting from the six-symmetrizations of prescribed powers at arbitrarily large compatible lengths $Dm$, with total $	au$-weight at least that base raised to $6Dm$. The original profile is unchanged.
--
--   This is the object-167 value endpoint at the exact rate of the More-Asymmetry re-emitted scalar ledger (its `rateFloor` for this row). It does not assert that the full fourth-power surplus or the final matrix-multiplication exponent bound has been completed.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 7, with the regional extraction of Alman, Duan, Vassilevska Williams, Xu, Xu, Zhou, More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v2, Section 6. Object-167 data generated from the released q=5 fourth-power certificate.

import Definitions.Def_mme_dwz_positive_341_regional_profile_data
import Definitions.Def_mme_complete_split_cw_fourth_labels

open MME MME.StothersFourth MME.CompleteSplit.CWFourth MME.DWZRestrictedValue
universe u
set_option autoImplicit false

theorem mme_dwz_positive_341_original_profile_value {K : Type u} [Field K] :
    HasPrescribedZSixRestrictionValueAtLeast
      (cwFourthConstituent K 5 3 4 1)
      (constituentBasis K 5 3 4 1 2)
      (fun a : LiftedCoarseCoordinate.{u} 5 1 ↦ cwSquarePairGrade 5 a.down.val.1)
      DWZPositiveComponent341.parentProfile
      (790643 / 1000000) (Real.exp (6159531789539 / 1000000000000)) := by sorry
