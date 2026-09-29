-- Prove2me | Theorems.Thm_mme_dwz_fourth_literal022_nineteen_prescribedZ_endpoints
-- name    : mme_dwz_fourth_literal022_nineteen_prescribedZ_endpoints
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-16T08:10:54.155676+00:00
-- url     : https://prove2.me/theorems/3cdc66e3-ac2e-4dee-bbcf-a87ca59fc984
-- title:
--   Nineteen exact prescribed-Z endpoints for the canonical q=5 022 component
-- statement:
--   Let $T_{022}$ be the canonical $(0,2,2)$ component of $\mathrm{CW}_5^{\otimes2}$ over any field, equipped with its canonical coarse-block $Z$ basis and left fine grade. For each of the nineteen published fourth-power records, let $p_i$ be its exact rational split profile and $r_i$ its stored rational logarithmic rate. At $\tau=790643/1000000$, the prescribed-$Z$ six-symmetric restriction value satisfies
--
--   $$V^{(6),\mathrm{restr}}_\tau(T_{022},p_i)\ge\exp(r_i).$$
--
--   Precisely, every strict positive lower base has actual finite matrix-multiplication direct-sum restriction witnesses at arbitrarily large compatible indices and physical lengths. This supplies all nineteen literal $(0,2,2)$ component endpoints from the data, without assuming any global fourth-power extraction. It does not assert the final fourth-power surplus theorem.
-- source:
--   Corollary of public theorem mme_dwz_canonical022_prescribed_z_six_restriction_value (fd56a1db-f79e-4cdf-bd90-20510fcc08d9), whose value is exp(tau H(p))*5^(2 tau p1), using the exact component data from the q=5 fourth-power certificate. Duan, Wu, Zhou, https://arxiv.org/html/2210.10173v5, Sections 6.3 and 8.3; this nineteen-row corollary is not separately numbered in the paper.

import Definitions.Def_mme_dwz_fourth_literal022_row_data
import Definitions.Def_mme_dwz_component_word_projection
import Definitions.Def_mme_dwz_cw_square_restricted_central_power_words

open BigOperators Module
open MME MME.DWZComponentRestriction MME.DWZRestrictedValue MME.DWZFineChannel

universe u
set_option autoImplicit false

open MME.ZEndpoint022PublicRows

theorem mme_dwz_fourth_literal022_nineteen_prescribedZ_endpoints (K : Type u) [Field K] (i : Fin 19) :
    let bZ : Basis (LiftedCoarsePair.{u} 5 2) K ((Central022Block K 5).V 2) :=
      (coarseClassBasis (K := K) 5 2 2).reindex Equiv.ulift.symm
    HasPrescribedZSixRestrictionValueAtLeast (Central022Block K 5) bZ
      LiftedCoarsePair.leftGrade (profile i) (790643 / 1000000 : ℝ)
      (Real.exp ((rows i).rate : ℝ))  := by sorry
