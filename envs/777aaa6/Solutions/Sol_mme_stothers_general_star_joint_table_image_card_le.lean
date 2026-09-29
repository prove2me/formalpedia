-- Prove2me | solution 1 for mme_stothers_general_star_joint_table_image_card_le
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-09-08T05:25:59.154989+00:00
-- url     : https://prove2.me/submissions/c53d5e12-f974-44f1-8e3e-e454e2e8ad97

import Definitions.Def_mme_stothers_general_outer_profile
import Theorems.Thm_mme_bounded_natural_table_family_card_le

open MME BigOperators

set_option autoImplicit false
set_option warningAsError true

theorem solution
    (base : Fin 10 → ℕ) (m : ℕ)
    (E : Finset (MME.StothersFourth.GenMarginalSupportedAddress base m))
    (a : MME.StothersFourth.GenMarginalSupportedAddress base m) (i : Fin 3) :
    ((E.filter (fun b ↦ b.1 i = a.1 i)).image
      MME.StothersFourth.genHashJointTable).card ≤
        (MME.StothersFourth.genOuterLength base m + 1) ^ 45 := by
  classical
  let Star := E.filter (fun b ↦ b.1 i = a.1 i)
  let Tables := Star.image MME.StothersFourth.genHashJointTable
  change Tables.card ≤ (MME.StothersFourth.genOuterLength base m + 1) ^ 45
  have h := mme_bounded_natural_table_family_card_le Tables
    (MME.StothersFourth.genOuterLength base m) (by
      intro k hk sigma
      rcases Finset.mem_image.mp hk with ⟨b, hb, rfl⟩
      change Fintype.card
        {j : Fin (MME.StothersFourth.genOuterLength base m) //
          MME.StothersFourth.genHashSupportedTypeAt b j = sigma} ≤
            MME.StothersFourth.genOuterLength base m
      simpa only [Fintype.card_fin] using
        (Fintype.card_subtype_le
          (fun j : Fin (MME.StothersFourth.genOuterLength base m) ↦
            MME.StothersFourth.genHashSupportedTypeAt b j = sigma)))
  have hcard : Fintype.card MME.StothersFourth.GenHashSupportTriple = 45 := by
    decide
  simpa only [hcard] using h
