-- Prove2me | Theorems.Thm_mme_dwz_positive_161_original_profile_value
-- name    : mme_dwz_positive_161_original_profile_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-19T16:59:49.254986+00:00
-- url     : https://prove2.me/theorems/2567e339-adff-4358-809c-85dfe41c578e
-- title:
--   Original prescribed-profile {1,6,1}$ value at the exact q5 ledger rate
-- statement:
--   Let $T_{1,6,1}$ be the actual canonical $(1,6,1)$ constituent of the fourth power of the Coppersmith–Winograd tensor $CW_5$, over an arbitrary field. Retain the original rational prescribed Z-split profile of released object 154: its Z-coordinate is $k = 1$, so the profile records the left grade $k_1 \in \{0,1\}$, with denominator $D = 10^{30}$ and count vector
--
--   $$(499999836852560862758332349976,\ 500000163147439137241667650024,\ 0,\ 0,\ 0).$$
--
--   At $\tau = 790643/1000000$, the restriction-based six-symmetrized value certificate for this exact profile is at least
--
--   $$\exp\!\left(\frac{2096791343139}{500000000000}\right).$$
--
--   Explicitly, every positive strict lower base has actual finite direct sums of matrix-multiplication tensors restricting from the six-symmetrizations of prescribed powers at arbitrarily large compatible lengths $Dm$, with total $\tau$-weight at least that base raised to $6Dm$. The original profile is unchanged. This is the object-154 value endpoint at the exact rate of the kernel-checked scalar ledger; it does not assert that the full fourth-power surplus or the final matrix-multiplication exponent bound has been completed.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definition 3.9 and Section 7 (Claims 7.1-7.2, Equation (34)). Exact object-154 rational replay: target rate and retained floor are the rateFloor and retainedFloor of ledger node 63 in the kernel-checked scalar recurrence ledger; child coefficients agree exactly with that ledger node.

import Definitions.Def_mme_dwz_positive_161_regional_profile_data
import Definitions.Def_mme_complete_split_cw_fourth_labels

open MME MME.StothersFourth MME.CompleteSplit.CWFourth MME.DWZRestrictedValue
universe u
set_option autoImplicit false

theorem mme_dwz_positive_161_original_profile_value
    {K : Type u} [Field K] :
    HasPrescribedZSixRestrictionValueAtLeast
      (cwFourthConstituent K 5 1 6 1)
      (constituentBasis K 5 1 6 1 2)
      (fun a : LiftedCoarseCoordinate.{u} 5 1 ↦ cwSquarePairGrade 5 a.down.val.1)
      DWZPositiveComponent161.parentProfile
      (790643 / 1000000) (Real.exp (2096791343139 / 500000000000)) := by sorry
