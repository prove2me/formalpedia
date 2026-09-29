-- Prove2me | Theorems.Thm_mme_dwz_positive_224_original_profile_value_above_ledger_rate
-- name    : mme_dwz_positive_224_original_profile_value_above_ledger_rate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-21T17:35:36.481454+00:00
-- url     : https://prove2.me/theorems/66f96235-3b04-4359-9b37-6800af9db4a6
-- title:
--   Positive fourth component T_{2,2,4}: original-profile value above the ledger rate
-- statement:
--   Let $T_{2,2,4}$ be the actual canonical $(2,2,4)$ constituent of the fourth power of the Coppersmith–Winograd tensor $CW_5$, over an arbitrary field. Retain the original rational prescribed Z-split profile of released object 158. Its Z-coordinate is $k = 4$, so the profile records the left grade, with denominator $D = 1000000000000000000000000000000$ and count vector
--
--   $$(15323329413099431755145615,\ 72025157105844115992386733216,\ 855919052397413832790945047167,\ 72025143809587818937469547462,\ 15323357741132847443526540).$$
--
--   At $\tau = 790643/1000000$, the restriction-based six-symmetrized value certificate for this exact profile is at least
--
--   $$\exp\!\left(\frac{6404755419211}{1000000000000}\right).$$
--
--   Explicitly, every positive strict lower base has actual finite direct sums of matrix-multiplication tensors restricting from the six-symmetrizations of prescribed powers at arbitrarily large compatible lengths $Dm$, with total $\tau$-weight at least that base raised to $6Dm$. The original profile is unchanged.
--
--   This is the object-158 value endpoint strictly above (by $10^{-9}$) the rate of the More-Asymmetry re-emitted scalar ledger (its `rateFloor` for this row), as needed to pass to ordinary six-symmetrized values. It does not assert that the full fourth-power surplus or the final matrix-multiplication exponent bound has been completed.
-- source:
--   Duan-Wu-Zhou fourth-power recursive construction (https://arxiv.org/html/2210.10173v5, section 7) combined with the More-Asymmetry regional extraction (https://arxiv.org/html/2404.16349v2, section 6). Exact finite or asymptotic-rate statement as written; no exponent claim.

import Definitions.Def_mme_dwz_positive_224_regional_profile_data
import Definitions.Def_mme_complete_split_cw_fourth_labels

open MME MME.StothersFourth MME.CompleteSplit.CWFourth MME.DWZRestrictedValue
universe u
set_option autoImplicit false

theorem mme_dwz_positive_224_original_profile_value_above_ledger_rate {K : Type u} [Field K] :
    HasPrescribedZSixRestrictionValueAtLeast
      (cwFourthConstituent K 5 2 2 4)
      (constituentBasis K 5 2 2 4 2)
      (fun a : LiftedCoarseCoordinate.{u} 5 4 ↦ cwSquarePairGrade 5 a.down.val.1)
      DWZPositiveComponent224.parentProfile
      (790643 / 1000000) (Real.exp (6404755419211 / 1000000000000)) := by sorry
