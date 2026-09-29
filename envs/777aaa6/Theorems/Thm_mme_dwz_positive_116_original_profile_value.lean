-- Prove2me | Theorems.Thm_mme_dwz_positive_116_original_profile_value
-- name    : mme_dwz_positive_116_original_profile_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-19T16:00:46.862983+00:00
-- url     : https://prove2.me/theorems/f701785e-63d0-4c0b-969a-21a94f0c1844
-- title:
--   Original prescribed-profile T116 value at the exact q5 ledger rate
-- statement:
--   Let $T_{1,1,6}$ be the actual canonical $(1,1,6)$ constituent of the fourth power of the Coppersmith–Winograd tensor $CW_5$, over an arbitrary field. Retain the original rational prescribed Z-split profile with denominator $D=10^{30}$ and count vector
--
--   $$
--   (0,0,
--   15632850634043171218716057,
--   999968734317748997496639110491,
--   15632831616959332142173452).
--   $$
--
--   At $\tau=790643/1000000$, the restriction-based six-symmetrized value certificate for this exact profile is at least
--
--   $$
--   \exp\!\left(\frac{32056585721}{7812500000}\right).
--   $$
--
--   Explicitly, every positive strict lower base has actual finite direct sums of matrix-multiplication tensors restricting from the six-symmetrizations of prescribed powers at arbitrarily large compatible lengths $Dm$, with total $\tau$-weight at least that base raised to $6Dm$. The original profile is unchanged. This is the original positive-parent object-149 value endpoint; it is not a theorem asserting that the full fourth-power surplus or the final matrix-multiplication exponent bound has been completed.
-- source:
--   Exact object-149 rational replay of the recursive fourth-power construction in Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Sections 3 and 7. The numerical endpoint is a derived certificate for the unchanged original input profile, not a claim that the full paper or final exponent bound is proved.

import Definitions.Def_mme_dwz_positive_116_regional_profile_data
import Definitions.Def_mme_complete_split_cw_fourth_labels

open MME MME.StothersFourth MME.CompleteSplit.CWFourth MME.DWZRestrictedValue
universe u
set_option autoImplicit false

theorem mme_dwz_positive_116_original_profile_value
    {K : Type u} [Field K] :
    HasPrescribedZSixRestrictionValueAtLeast
      (cwFourthConstituent K 5 1 1 6)
      (constituentBasis K 5 1 1 6 2)
      (fun a : LiftedCoarseCoordinate.{u} 5 6 ↦ cwSquarePairGrade 5 a.down.val.1)
      DWZPositiveComponent116.parentProfile
      (790643 / 1000000) (Real.exp (32056585721 / 7812500000)) := by sorry
