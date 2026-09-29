-- Prove2me | Theorems.Thm_mme_dwz_positive_512_original_profile_value_at_ledger_rate
-- name    : mme_dwz_positive_512_original_profile_value_at_ledger_rate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-21T16:43:05.236922+00:00
-- url     : https://prove2.me/theorems/a50146e6-9220-405d-841b-1749a1c22a68
-- title:
--   Positive fourth component T_{5,1,2}: original-profile value at the ledger rate
-- statement:
--   Let $T_{5,1,2}$ be the actual canonical $(5,1,2)$ constituent of the fourth power of the Coppersmith–Winograd tensor $CW_5$, over an arbitrary field. Retain the original rational prescribed Z-split profile of released object 175. Its Z-coordinate is $k = 2$, so the profile records the left grade, with denominator $D = 1000000000000000000000000000000$ and count vector
--
--   $$(182504178883141869154180135523,\ 634992871318010940641369847427,\ 182502949798847190204450017050,\ 0,\ 0).$$
--
--   At $	au = 790643/1000000$, the restriction-based six-symmetrized value certificate for this exact profile is at least
--
--   $$\exp\!\left(rac{2730192631343}{500000000000}ight).$$
--
--   Explicitly, every positive strict lower base has actual finite direct sums of matrix-multiplication tensors restricting from the six-symmetrizations of prescribed powers at arbitrarily large compatible lengths $Dm$, with total $	au$-weight at least that base raised to $6Dm$. The original profile is unchanged.
--
--   This is the object-175 value endpoint at the exact rate of the More-Asymmetry re-emitted scalar ledger (its `rateFloor` for this row). It does not assert that the full fourth-power surplus or the final matrix-multiplication exponent bound has been completed.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 7, with the regional extraction of Alman, Duan, Vassilevska Williams, Xu, Xu, Zhou, More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v2, Section 6. Object-175 data generated from the released q=5 fourth-power certificate.

import Definitions.Def_mme_dwz_positive_512_regional_profile_data
import Definitions.Def_mme_complete_split_cw_fourth_labels

open MME MME.StothersFourth MME.CompleteSplit.CWFourth MME.DWZRestrictedValue
universe u
set_option autoImplicit false

theorem mme_dwz_positive_512_original_profile_value_at_ledger_rate {K : Type u} [Field K] :
    HasPrescribedZSixRestrictionValueAtLeast
      (cwFourthConstituent K 5 5 1 2)
      (constituentBasis K 5 5 1 2 2)
      (fun a : LiftedCoarseCoordinate.{u} 5 2 ↦ cwSquarePairGrade 5 a.down.val.1)
      DWZPositiveComponent512.parentProfile
      (790643 / 1000000) (Real.exp (2730192631343 / 500000000000)) := by sorry
