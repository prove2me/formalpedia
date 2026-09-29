-- Prove2me | Theorems.Thm_mme_dwz_positive_134_original_profile_value
-- name    : mme_dwz_positive_134_original_profile_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-21T11:24:01.810647+00:00
-- url     : https://prove2.me/theorems/37948958-d429-4090-a60c-ee159279c9f4
-- title:
--   Positive fourth component T_{1,3,4}: original-profile value at the ledger rate
-- statement:
--   Let $T_{1,3,4}$ be the actual canonical $(1,3,4)$ constituent of the fourth power of the Coppersmith–Winograd tensor $CW_5$, over an arbitrary field. Retain the original rational prescribed Z-split profile of released object 151. Its Z-coordinate is $k = 4$, so the profile records the left grade $k_1 \in \{0,\dots,4\}$, with denominator $D = 10^{30}$ and count vector
--
--   $$(15464618093589756823253913,\ 72089434438510093271636731687,\ 855790219898924325342553259309,\ 72089416398130957534313182364,\ 15464646341034094673572727).$$
--
--   At $\tau = 790643/1000000$, the restriction-based six-symmetrized value certificate for this exact profile is at least
--
--   $$\exp\!\left(\frac{769869971361}{125000000000}\right).$$
--
--   Explicitly, every positive strict lower base has actual finite direct sums of matrix-multiplication tensors restricting from the six-symmetrizations of prescribed powers at arbitrarily large compatible lengths $Dm$, with total $\tau$-weight at least that base raised to $6Dm$. The original profile is unchanged.
--
--   This is the object-151 value endpoint at the exact rate of the More-Asymmetry re-emitted scalar ledger (its `rateFloor` for this row). It does not assert that the full fourth-power surplus or the final matrix-multiplication exponent bound has been completed.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 7 (Claims 7.1-7.3), with the regional extraction of Alman, Duan, Vassilevska Williams, Xu, Xu, Zhou, More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v2, Section 6. Target rate: rateFloor of the object-151 row in the More-Asymmetry re-emitted scalar ledger.

import Definitions.Def_mme_dwz_positive_134_regional_profile_data
import Definitions.Def_mme_complete_split_cw_fourth_labels

open MME MME.StothersFourth MME.CompleteSplit.CWFourth MME.DWZRestrictedValue
universe u
set_option autoImplicit false

theorem mme_dwz_positive_134_original_profile_value {K : Type u} [Field K] :
    HasPrescribedZSixRestrictionValueAtLeast
      (cwFourthConstituent K 5 1 3 4)
      (constituentBasis K 5 1 3 4 2)
      (fun a : LiftedCoarseCoordinate.{u} 5 4 ↦ cwSquarePairGrade 5 a.down.val.1)
      DWZPositiveComponent134.parentProfile
      (790643 / 1000000) (Real.exp (769869971361 / 125000000000)) := by sorry
