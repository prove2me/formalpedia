-- Prove2me | solution 1 for MME.StothersFourth.mme_stothers_fixed_full_marginal_star_degree_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T20:50:10.234133+00:00
-- url     : https://prove2.me/submissions/5b1bd83d-24c9-48b7-811b-e5e0188e2e96

import Definitions.Def_mme_stothers_fixed_outer_profile
import Definitions.Def_mme_stothers_fixed_joint_tables
import Theorems.Thm_MME_StothersFourth_mme_stothers_fixed_star_joint_table_image_card_le
import Theorems.Thm_MME_StothersFourth_mme_stothers_fixed_star_joint_table_fiber_le

open MME BigOperators

set_option autoImplicit false
set_option warningAsError true

theorem solution
    (m : ℕ) (hm : 0 < m)
    (E : Finset (MME.StothersFourth.FixedMarginalSupportedAddress m))
    (a : MME.StothersFourth.FixedMarginalSupportedAddress m) (i : Fin 3) :
    (E.filter (fun b ↦ b.1 i = a.1 i)).card ≤
      (MME.StothersFourth.fixedOuterLength m + 1) ^ 45 *
        ((6 * (MME.StothersFourth.fixedOuterLength m + 1)) ^ 45 *
          MME.StothersFourth.fixedHashTargetStarDegree m) := by
  classical
  have hfiber : ∀ k ∈
      (E.filter (fun b ↦ b.1 i = a.1 i)).image
        MME.StothersFourth.fixedHashJointTable,
      ((E.filter (fun b ↦ b.1 i = a.1 i)).filter
        (fun b ↦ MME.StothersFourth.fixedHashJointTable b = k)).card ≤
          (6 * (MME.StothersFourth.fixedOuterLength m + 1)) ^ 45 *
            MME.StothersFourth.fixedHashTargetStarDegree m := by
    intro k hk
    exact MME.StothersFourth.mme_stothers_fixed_star_joint_table_fiber_le
      m hm E a i k hk
  have hTableBound :
      ((E.filter (fun b ↦ b.1 i = a.1 i)).image
        MME.StothersFourth.fixedHashJointTable).card ≤
          (MME.StothersFourth.fixedOuterLength m + 1) ^ 45 :=
    MME.StothersFourth.mme_stothers_fixed_star_joint_table_image_card_le
      m E a i
  have hStar := Finset.card_le_mul_card_image
    (E.filter (fun b ↦ b.1 i = a.1 i))
    ((6 * (MME.StothersFourth.fixedOuterLength m + 1)) ^ 45 *
      MME.StothersFourth.fixedHashTargetStarDegree m) hfiber
  calc
    (E.filter (fun b ↦ b.1 i = a.1 i)).card ≤
        ((6 * (MME.StothersFourth.fixedOuterLength m + 1)) ^ 45 *
          MME.StothersFourth.fixedHashTargetStarDegree m) *
          ((E.filter (fun b ↦ b.1 i = a.1 i)).image
            MME.StothersFourth.fixedHashJointTable).card := hStar
    _ ≤ ((6 * (MME.StothersFourth.fixedOuterLength m + 1)) ^ 45 *
          MME.StothersFourth.fixedHashTargetStarDegree m) *
        (MME.StothersFourth.fixedOuterLength m + 1) ^ 45 :=
      Nat.mul_le_mul_left _ hTableBound
    _ = (MME.StothersFourth.fixedOuterLength m + 1) ^ 45 *
        ((6 * (MME.StothersFourth.fixedOuterLength m + 1)) ^ 45 *
          MME.StothersFourth.fixedHashTargetStarDegree m) :=
      Nat.mul_comm _ _
