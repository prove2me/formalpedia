-- Prove2me | solution 1 for MME.StothersFourth.mme_stothers_fixed_exact_target_star_degree_le_power100
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T21:21:47.66747+00:00
-- url     : https://prove2.me/submissions/0dca86d0-b3cd-4869-ae2c-872903b80b40

import Definitions.Def_mme_stothers_fixed_outer_profile
import Definitions.Def_mme_stothers_fixed_joint_tables
import Theorems.Thm_MME_StothersFourth_mme_stothers_fixed_full_marginal_star_degree_le

open MME BigOperators

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000

open MME.StothersFourth

theorem solution
    (m : ℕ) (hm : 0 < m)
    (i : Fin 3)
    (a : {a : FixedMarginalSupportedAddress m //
      FixedHasExactJointProfile a}) :
    Nat.card
        {b : FixedMarginalSupportedAddress m //
          b.1 i = a.1.1 i} ≤
      (6 * (fixedOuterLength m + 1)) ^ 100 *
        fixedHashTargetStarDegree m := by
  classical
  letI : Fintype (FixedOuterAddress m) :=
    inferInstanceAs (Fintype
      (Fin 3 → Fin (fixedOuterLength m) → Fin 9))
  letI : Fintype (FixedMarginalSupportedAddress m) :=
    inferInstanceAs (Fintype
      {b : FixedOuterAddress m //
        FixedCoordinatewiseSupported b ∧ FixedMarginallyRegular b})
  have hstar := mme_stothers_fixed_full_marginal_star_degree_le
    m hm (Finset.univ : Finset (FixedMarginalSupportedAddress m)) a.1 i
  have hcard :
      Nat.card
          {b : FixedMarginalSupportedAddress m // b.1 i = a.1.1 i} =
        ((Finset.univ : Finset (FixedMarginalSupportedAddress m)).filter
          (fun b ↦ b.1 i = a.1.1 i)).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hcard]
  let A := fixedOuterLength m + 1
  let B := 6 * A
  let D := fixedHashTargetStarDegree m
  have hAB : A ≤ B := by
    dsimp only [A, B]
    omega
  have hBpos : 0 < B := by
    dsimp only [B, A]
    omega
  have hpoly : A ^ 45 * B ^ 45 ≤ B ^ 100 := by
    calc
      A ^ 45 * B ^ 45 ≤ B ^ 45 * B ^ 45 :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hAB 45)
      _ = B ^ 90 := by rw [← pow_add]
      _ ≤ B ^ 100 := Nat.pow_le_pow_right hBpos (by omega)
  calc
    ((Finset.univ : Finset (FixedMarginalSupportedAddress m)).filter
        (fun b ↦ b.1 i = a.1.1 i)).card ≤
        A ^ 45 * (B ^ 45 * D) := by
      simpa only [A, B, D] using hstar
    _ = (A ^ 45 * B ^ 45) * D := by simp only [mul_assoc]
    _ ≤ B ^ 100 * D := Nat.mul_le_mul_right D hpoly
    _ = (6 * (fixedOuterLength m + 1)) ^ 100 *
        fixedHashTargetStarDegree m := rfl
