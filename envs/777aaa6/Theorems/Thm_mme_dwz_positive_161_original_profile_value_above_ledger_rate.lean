-- Prove2me | Theorems.Thm_mme_dwz_positive_161_original_profile_value_above_ledger_rate
-- name    : mme_dwz_positive_161_original_profile_value_above_ledger_rate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-21T18:14:47.62603+00:00
-- url     : https://prove2.me/theorems/147646a3-04df-4943-86c5-988f6eadb54b
-- title:
--   Positive fourth component T_{1,6,1}: original-profile value at the ledger rate
-- statement:
--   Let $T_{1,6,1}$ be the actual canonical $(1,6,1)$ constituent of the fourth power of the Coppersmith–Winograd tensor $CW_5$, over an arbitrary field. Retain the original rational prescribed Z-split profile of released object 154. Its Z-coordinate is $k = 1$, so the profile records the left grade, with denominator $D = 1000000000000000000000000000000$ and count vector
--
--   $$(499999836852560862758332349976,\ 500000163147439137241667650024,\ 0,\ 0,\ 0).$$
--
--   At $\tau = 790643/1000000$, the restriction-based six-symmetrized value certificate for this exact profile is at least
--
--   $$\exp\!\left(\frac{2096791343639}{500000000000}\right).$$
--
--   Explicitly, every positive strict lower base has actual finite direct sums of matrix-multiplication tensors restricting from the six-symmetrizations of prescribed powers at arbitrarily large compatible lengths $Dm$, with total $\tau$-weight at least that base raised to $6Dm$. The original profile is unchanged.
--
--   This is the object-154 value endpoint strictly above (by $10^{-9}$) the rate of the More-Asymmetry re-emitted scalar ledger (its `rateFloor` for this row), as needed to pass to ordinary six-symmetrized values. It does not assert that the full fourth-power surplus or the final matrix-multiplication exponent bound has been completed.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 7, with the regional extraction of Alman, Duan, Vassilevska Williams, Xu, Xu, Zhou, More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v2, Section 6. Object-154 data generated from the released q=5 fourth-power certificate.

import Definitions.Def_mme_dwz_positive_161_regional_profile_data
import Definitions.Def_mme_complete_split_cw_fourth_labels

open MME MME.StothersFourth MME.CompleteSplit.CWFourth MME.DWZRestrictedValue
universe u
set_option autoImplicit false

theorem mme_dwz_positive_161_original_profile_value_above_ledger_rate {K : Type u} [Field K] :
    HasPrescribedZSixRestrictionValueAtLeast
      (cwFourthConstituent K 5 1 6 1)
      (constituentBasis K 5 1 6 1 2)
      (fun a : LiftedCoarseCoordinate.{u} 5 1 ↦ cwSquarePairGrade 5 a.down.val.1)
      DWZPositiveComponent161.parentProfile
      (790643 / 1000000) (Real.exp (2096791343639 / 500000000000)) := by sorry
