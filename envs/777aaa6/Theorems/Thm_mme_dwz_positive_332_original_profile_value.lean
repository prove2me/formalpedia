-- Prove2me | Theorems.Thm_mme_dwz_positive_332_original_profile_value
-- name    : mme_dwz_positive_332_original_profile_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-21T17:51:17.72601+00:00
-- url     : https://prove2.me/theorems/99e4dc37-da6d-460b-9fa9-6616b8655116
-- title:
--   Positive fourth component T_{3,3,2}: original-profile value at the ledger rate
-- statement:
--   Let $T_{3,3,2}$ be the actual canonical $(3,3,2)$ constituent of the fourth power of the Coppersmith–Winograd tensor $CW_5$, over an arbitrary field. Retain the original rational prescribed Z-split profile of released object 166. Its Z-coordinate is $k = 2$, so the profile records the left grade, with denominator $D = 1000000000000000000000000000000$ and count vector
--
--   $$(182244070954619267895565448840,\ 635511971102645667357472221678,\ 182243957942735064746962329482,\ 0,\ 0).$$
--
--   At $\tau = 790643/1000000$, the restriction-based six-symmetrized value certificate for this exact profile is at least
--
--   $$\exp\!\left(\frac{6676023499877}{1000000000000}\right).$$
--
--   Explicitly, every positive strict lower base has actual finite direct sums of matrix-multiplication tensors restricting from the six-symmetrizations of prescribed powers at arbitrarily large compatible lengths $Dm$, with total $\tau$-weight at least that base raised to $6Dm$. The original profile is unchanged.
--
--   This is the object-166 value endpoint at the exact rate of the More-Asymmetry re-emitted scalar ledger (its `rateFloor` for this row). It does not assert that the full fourth-power surplus or the final matrix-multiplication exponent bound has been completed.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 7, with the regional extraction of Alman, Duan, Vassilevska Williams, Xu, Xu, Zhou, More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v2, Section 6. Object-166 data generated from the released q=5 fourth-power certificate.

import Definitions.Def_mme_dwz_positive_332_regional_profile_data
import Definitions.Def_mme_complete_split_cw_fourth_labels

open MME MME.StothersFourth MME.CompleteSplit.CWFourth MME.DWZRestrictedValue
universe u
set_option autoImplicit false

theorem mme_dwz_positive_332_original_profile_value {K : Type u} [Field K] :
    HasPrescribedZSixRestrictionValueAtLeast
      (cwFourthConstituent K 5 3 3 2)
      (constituentBasis K 5 3 3 2 2)
      (fun a : LiftedCoarseCoordinate.{u} 5 2 ↦ cwSquarePairGrade 5 a.down.val.1)
      DWZPositiveComponent332.parentProfile
      (790643 / 1000000) (Real.exp (6676023499877 / 1000000000000)) := by sorry
