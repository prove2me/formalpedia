-- Prove2me | Theorems.Thm_mme_dwz_positive_521_original_profile_value
-- name    : mme_dwz_positive_521_original_profile_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-19T22:06:23.970991+00:00
-- url     : https://prove2.me/theorems/8d026a46-b650-4c2f-87c3-e2912e14b923
-- title:
--   Original prescribed-profile $T_{5,2,1}$ value at the thin-route rate
-- statement:
--   Let $T_{5,2,1}$ be the actual canonical $(5,2,1)$ constituent of the fourth power of the Coppersmith–Winograd tensor $CW_5$, over an arbitrary field, with the unchanged original prescribed Z-split profile of released object 176 (`DWZPositiveComponent521.parentProfile`). At $\tau = 790643/1000000$, its restriction-based six-symmetrized value certificate is at least
--
--   $$\exp\!\left(\frac{5459911963257}{1000000000000}\right).$$
--
--   Explicitly, every positive strict lower base has actual finite direct sums of matrix-multiplication tensors restricting from the six-symmetrizations of prescribed powers at arbitrarily large compatible lengths, with total $\tau$-weight at least that base raised to $6$ times the length.
--
--   **Rate.** This is the *thin-route* rate: it does not use DWZ's asymmetric-hashing gain $\lambda$ for this component, so it is slightly below the released ledger rate $5.460385998309$. An exact offline replay of the scalar ledger recurrence, with this and the other five small-$\lambda$ $(1,2,5)$-type components lowered in the same way, still certifies a global value strictly above $2401$ (margin $1.70\times10^{-6}$ in log-rate over a certified upper bound for $\ln 2401$). A kernel-checked version of that regenerated ledger is not part of this theorem. This endpoint does not assert the full fourth-power surplus or the final exponent bound.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definition 3.9 and Section 7 (Claims 7.1-7.2, Equation (34) in the thin case). Object 176; child coefficients agree exactly with its node in the kernel-checked scalar recurrence ledger; retained floor is the certified thin six-mode rate rounded down to 10^-12.

import Definitions.Def_mme_dwz_positive_521_regional_profile_data
import Definitions.Def_mme_complete_split_cw_fourth_labels

open MME MME.StothersFourth MME.CompleteSplit.CWFourth MME.DWZRestrictedValue
universe u
set_option autoImplicit false

theorem mme_dwz_positive_521_original_profile_value
    {K : Type u} [Field K] :
    HasPrescribedZSixRestrictionValueAtLeast
      (cwFourthConstituent K 5 5 2 1)
      (constituentBasis K 5 5 2 1 2)
      (fun a : LiftedCoarseCoordinate.{u} 5 1 ↦ cwSquarePairGrade 5 a.down.val.1)
      DWZPositiveComponent521.parentProfile
      (790643 / 1000000) (Real.exp (5459911963257 / 1000000000000)) := by sorry
