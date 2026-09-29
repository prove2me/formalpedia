-- Prove2me | Theorems.Thm_mme_dwz_positive_143_original_profile_value_above_ledger_rate
-- name    : mme_dwz_positive_143_original_profile_value_above_ledger_rate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-21T17:17:24.413015+00:00
-- url     : https://prove2.me/theorems/9400104a-72e5-4656-bb27-499466ae45e6
-- title:
--   Positive fourth component T_{1,4,3}: original-profile value above the ledger rate
-- statement:
--   Let $T_{1,4,3}$ be the actual canonical $(1,4,3)$ constituent of the fourth power of the Coppersmith–Winograd tensor $CW_5$, over an arbitrary field. Retain the original rational prescribed Z-split profile of released object 152. Its Z-coordinate is $k = 3$, so the profile records the left grade, with denominator $D = 1000000000000000000000000000000$ and count vector
--
--   $$(13090639443859542902286822502,\ 486911371945649843418567510920,\ 486907202813598168056223734646,\ 13090785796892445622921931932,\ 0).$$
--
--   At $\tau = 790643/1000000$, the restriction-based six-symmetrized value certificate for this exact profile is at least
--
--   $$\exp\!\left(\frac{615953393693}{100000000000}\right).$$
--
--   Explicitly, every positive strict lower base has actual finite direct sums of matrix-multiplication tensors restricting from the six-symmetrizations of prescribed powers at arbitrarily large compatible lengths $Dm$, with total $\tau$-weight at least that base raised to $6Dm$. The original profile is unchanged.
--
--   This is the object-152 value endpoint strictly above (by $10^{-9}$) the rate of the More-Asymmetry re-emitted scalar ledger (its `rateFloor` for this row), as needed to pass to ordinary six-symmetrized values. It does not assert that the full fourth-power surplus or the final matrix-multiplication exponent bound has been completed.
-- source:
--   Duan-Wu-Zhou fourth-power recursive construction (https://arxiv.org/html/2210.10173v5, section 7) combined with the More-Asymmetry regional extraction (https://arxiv.org/html/2404.16349v2, section 6). Exact finite or asymptotic-rate statement as written; no exponent claim.

import Definitions.Def_mme_dwz_positive_143_regional_profile_data
import Definitions.Def_mme_complete_split_cw_fourth_labels

open MME MME.StothersFourth MME.CompleteSplit.CWFourth MME.DWZRestrictedValue
universe u
set_option autoImplicit false

theorem mme_dwz_positive_143_original_profile_value_above_ledger_rate {K : Type u} [Field K] :
    HasPrescribedZSixRestrictionValueAtLeast
      (cwFourthConstituent K 5 1 4 3)
      (constituentBasis K 5 1 4 3 2)
      (fun a : LiftedCoarseCoordinate.{u} 5 3 ↦ cwSquarePairGrade 5 a.down.val.1)
      DWZPositiveComponent143.parentProfile
      (790643 / 1000000) (Real.exp (615953393693 / 100000000000)) := by sorry
