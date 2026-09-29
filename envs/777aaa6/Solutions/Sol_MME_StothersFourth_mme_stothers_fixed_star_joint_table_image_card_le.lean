-- Prove2me | solution 1 for MME.StothersFourth.mme_stothers_fixed_star_joint_table_image_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T20:53:03.092769+00:00
-- url     : https://prove2.me/submissions/573faac5-267a-4bac-a27d-3d3bd2665020

import Definitions.Def_mme_stothers_fixed_outer_profile
import Definitions.Def_mme_stothers_fixed_joint_tables
import Theorems.Thm_mme_bounded_natural_table_family_card_le

open MME BigOperators

set_option autoImplicit false
set_option warningAsError true

theorem solution
    (m : ℕ)
    (E : Finset (MME.StothersFourth.FixedMarginalSupportedAddress m))
    (a : MME.StothersFourth.FixedMarginalSupportedAddress m) (i : Fin 3) :
    ((E.filter (fun b ↦ b.1 i = a.1 i)).image
      MME.StothersFourth.fixedHashJointTable).card ≤
        (MME.StothersFourth.fixedOuterLength m + 1) ^ 45 := by
  classical
  let Star := E.filter (fun b ↦ b.1 i = a.1 i)
  let Tables := Star.image MME.StothersFourth.fixedHashJointTable
  change Tables.card ≤ (MME.StothersFourth.fixedOuterLength m + 1) ^ 45
  have h := mme_bounded_natural_table_family_card_le Tables
    (MME.StothersFourth.fixedOuterLength m) (by
      intro k hk sigma
      rcases Finset.mem_image.mp hk with ⟨b, hb, rfl⟩
      change Fintype.card
        {j : Fin (MME.StothersFourth.fixedOuterLength m) //
          MME.StothersFourth.fixedHashSupportedTypeAt b j = sigma} ≤
            MME.StothersFourth.fixedOuterLength m
      simpa only [Fintype.card_fin] using
        (Fintype.card_subtype_le
          (fun j : Fin (MME.StothersFourth.fixedOuterLength m) ↦
            MME.StothersFourth.fixedHashSupportedTypeAt b j = sigma)))
  have hcard : Fintype.card MME.StothersFourth.FixedHashSupportTriple = 45 := by
    decide
  simpa only [hcard] using h
