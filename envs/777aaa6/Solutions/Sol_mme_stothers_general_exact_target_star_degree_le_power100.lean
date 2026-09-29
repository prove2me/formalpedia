-- Prove2me | solution 1 for mme_stothers_general_exact_target_star_degree_le_power100
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-09-08T05:35:33.509766+00:00
-- url     : https://prove2.me/submissions/89589d52-7ff9-425d-ac82-54d0838eba7f

import Definitions.Def_mme_stothers_general_outer_profile
import Definitions.Def_mme_modern_entropy_data
import Theorems.Thm_mme_stothers_general_star_joint_table_image_card_le
import Theorems.Thm_mme_stothers_general_star_joint_table_fiber_le

open MME BigOperators

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000

open MME.StothersFourth

theorem solution
    (base bstar : Fin 10 → ℕ) (m : ℕ) (hm : 0 < m)
    (hbase : ∀ r, 0 < base r)
    (hsame : ∀ j, genMarginalBaseCount bstar j = genMarginalBaseCount base j)
    (hcond : ∀ k : GenHashJointMultiplicityTable,
      (∀ l : Fin 3, ∀ j : Fin 9,
        (∑ sigma : {sigma : GenHashSupportTriple // sigma.1 l = j},
          k sigma.1) = genMarginalCount base m j) →
      ∀ i : Fin 3,
      (∑ j : Fin 9, (genMarginalCount base m j : ℝ) *
        mme_modern_entropyBits
          (fun sigma : {sigma : GenHashSupportTriple // sigma.1 i = j} ↦
            (k sigma.1 : ℝ) / (genMarginalCount base m j : ℝ))) ≤
      ∑ j : Fin 9, (genMarginalCount base m j : ℝ) *
        mme_modern_entropyBits
          (fun sigma : {sigma : GenHashSupportTriple // sigma.1 i = j} ↦
            (genHashTargetJointTable bstar m sigma.1 : ℝ) /
              (genMarginalCount base m j : ℝ)))
    (i : Fin 3)
    (a : {a : GenMarginalSupportedAddress base m //
      GenHasExactJointProfile a}) :
    Nat.card {b : GenMarginalSupportedAddress base m // b.1 i = a.1.1 i} ≤
      (6 * (genOuterLength base m + 1)) ^ 100 *
        genHashTargetStarDegree bstar m := by
  classical
  letI : Fintype (GenOuterAddress base m) :=
    inferInstanceAs (Fintype
      (Fin 3 → Fin (genOuterLength base m) → Fin 9))
  letI : Fintype (GenMarginalSupportedAddress base m) :=
    inferInstanceAs (Fintype
      {b : GenOuterAddress base m //
        GenCoordinatewiseSupported b ∧ GenMarginallyRegular b})
  set E : Finset (GenMarginalSupportedAddress base m) := Finset.univ with hE
  have hfiber : ∀ k ∈ (E.filter (fun b ↦ b.1 i = a.1.1 i)).image
      genHashJointTable,
      ((E.filter (fun b ↦ b.1 i = a.1.1 i)).filter
        (fun b ↦ genHashJointTable b = k)).card ≤
          (6 * (genOuterLength base m + 1)) ^ 45 *
            genHashTargetStarDegree bstar m := by
    intro k hk
    exact mme_stothers_general_star_joint_table_fiber_le
      base bstar m hm hbase hsame hcond E a.1 i k hk
  have hTableBound :
      ((E.filter (fun b ↦ b.1 i = a.1.1 i)).image genHashJointTable).card ≤
          (genOuterLength base m + 1) ^ 45 :=
    mme_stothers_general_star_joint_table_image_card_le base m E a.1 i
  have hStar := Finset.card_le_mul_card_image
    (E.filter (fun b ↦ b.1 i = a.1.1 i))
    ((6 * (genOuterLength base m + 1)) ^ 45 *
      genHashTargetStarDegree bstar m) hfiber
  have hcard :
      Nat.card {b : GenMarginalSupportedAddress base m // b.1 i = a.1.1 i} =
        (E.filter (fun b ↦ b.1 i = a.1.1 i)).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hcard]
  set A := genOuterLength base m + 1 with hA
  set B := 6 * A with hB
  set D := genHashTargetStarDegree bstar m with hD
  have hAB : A ≤ B := by
    dsimp only [hA, hB]
    omega
  have hBpos : 0 < B := by
    dsimp only [hB, hA]
    omega
  have hpoly : A ^ 45 * B ^ 45 ≤ B ^ 100 := by
    calc
      A ^ 45 * B ^ 45 ≤ B ^ 45 * B ^ 45 :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hAB 45)
      _ = B ^ 90 := by rw [← pow_add]
      _ ≤ B ^ 100 := Nat.pow_le_pow_right hBpos (by omega)
  calc
    (E.filter (fun b ↦ b.1 i = a.1.1 i)).card ≤
        (B ^ 45 * D) *
          ((E.filter (fun b ↦ b.1 i = a.1.1 i)).image
            genHashJointTable).card := hStar
    _ ≤ (B ^ 45 * D) * A ^ 45 := Nat.mul_le_mul_left _ hTableBound
    _ = (A ^ 45 * B ^ 45) * D := by ring
    _ ≤ B ^ 100 * D := Nat.mul_le_mul_right _ hpoly
