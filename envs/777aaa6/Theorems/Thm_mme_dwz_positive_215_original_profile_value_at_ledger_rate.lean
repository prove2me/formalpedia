-- Prove2me | Theorems.Thm_mme_dwz_positive_215_original_profile_value_at_ledger_rate
-- name    : mme_dwz_positive_215_original_profile_value_at_ledger_rate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-21T16:46:03.913952+00:00
-- url     : https://prove2.me/theorems/6a4b0ec8-1168-484a-a8c7-facd3649267f
-- title:
--   Positive fourth component T_{2,1,5}: original-profile value at the ledger rate
-- statement:
--   Let $T_{2,1,5}$ be the actual canonical $(2,1,5)$ constituent of the fourth power of the Coppersmith–Winograd tensor $CW_5$, over an arbitrary field. Retain the original rational prescribed Z-split profile of released object 157. Its Z-coordinate is $k = 5$, so the profile records the left grade, with denominator $D = 1000000000000000000000000000000$ and count vector
--
--   $$(0,\ 1391630958173011920935089105,\ 498608739167650629785623212965,\ 498607981201181818955886747224,\ 1391648672994539337554950706).$$
--
--   At $	au = 790643/1000000$, the restriction-based six-symmetrized value certificate for this exact profile is at least
--
--   $$\exp\!\left(rac{5457358688867}{1000000000000}ight).$$
--
--   Explicitly, every positive strict lower base has actual finite direct sums of matrix-multiplication tensors restricting from the six-symmetrizations of prescribed powers at arbitrarily large compatible lengths $Dm$, with total $	au$-weight at least that base raised to $6Dm$. The original profile is unchanged.
--
--   This is the object-157 value endpoint at the exact rate of the More-Asymmetry re-emitted scalar ledger (its `rateFloor` for this row). It does not assert that the full fourth-power surplus or the final matrix-multiplication exponent bound has been completed.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 7, with the regional extraction of Alman, Duan, Vassilevska Williams, Xu, Xu, Zhou, More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v2, Section 6. Object-157 data generated from the released q=5 fourth-power certificate.

import Definitions.Def_mme_dwz_positive_215_regional_profile_data
import Definitions.Def_mme_complete_split_cw_fourth_labels

open MME MME.StothersFourth MME.CompleteSplit.CWFourth MME.DWZRestrictedValue
universe u
set_option autoImplicit false

theorem mme_dwz_positive_215_original_profile_value_at_ledger_rate {K : Type u} [Field K] :
    HasPrescribedZSixRestrictionValueAtLeast
      (cwFourthConstituent K 5 2 1 5)
      (constituentBasis K 5 2 1 5 2)
      (fun a : LiftedCoarseCoordinate.{u} 5 5 ↦ cwSquarePairGrade 5 a.down.val.1)
      DWZPositiveComponent215.parentProfile
      (790643 / 1000000) (Real.exp (5457358688867 / 1000000000000)) := by sorry
