-- Prove2me | solution 1 for MME.StothersFourth.mme_stothers_fixed_exact_target_count_factorization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T21:19:30.49714+00:00
-- url     : https://prove2.me/submissions/41c2c8c8-0a93-47bb-b0be-06ea0c3847f1

import Definitions.Def_mme_stothers_fixed_outer_profile
import Definitions.Def_mme_stothers_fixed_joint_tables
import Theorems.Thm_mme_stothers_fixed_outer_profile_arithmetic
import Theorems.Thm_MME_StothersFourth_mme_stothers_fixed_target_joint_table_marginal
import Theorems.Thm_MME_StothersFourth_mme_stothers_fixed_exact_target_subtype_nat_card

open MME BigOperators

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

open MME.StothersFourth

theorem solution (m : ℕ) :
    let N := fixedOuterLength m
    let V : ℝ :=
      (N.factorial : ℝ) /
        ∏ j : Fin 9, ((fixedMarginalCount m j).factorial : ℝ)
    (Nat.card
        {a : FixedMarginalSupportedAddress m //
          FixedHasExactJointProfile a} : ℝ) =
        V * (fixedHashTargetStarDegree m : ℝ) ∧
      1 ≤ fixedHashTargetStarDegree m := by
  dsimp only
  classical
  let N := fixedOuterLength m
  let M := ∏ j : Fin 9, (fixedMarginalCount m j).factorial
  let B := ∏ sigma : FixedHashSupportTriple,
    (fixedHashTargetJointTable m sigma).factorial
  have hMcast : (M : ℝ) =
      ∏ j : Fin 9, ((fixedMarginalCount m j).factorial : ℝ) := by
    simp only [M, Nat.cast_prod]
  rw [← hMcast]
  change
    (Nat.card
        {a : FixedMarginalSupportedAddress m //
          FixedHasExactJointProfile a} : ℝ) =
        ((N.factorial : ℝ) / (M : ℝ)) *
          (fixedHashTargetStarDegree m : ℝ) ∧
      1 ≤ fixedHashTargetStarDegree m
  have hmarginalSum :
      (∑ j : Fin 9, fixedMarginalCount m j) = N := by
    simp only [fixedMarginalCount]
    rw [← Finset.mul_sum,
      mme_stothers_fixed_outer_profile_arithmetic.2.2.2.2.1]
    simp only [N, fixedOuterLength]
    ac_rfl
  have hMdivN : M ∣ N.factorial := by
    have h := Nat.prod_factorial_dvd_factorial_sum
      (Finset.univ : Finset (Fin 9)) (fixedMarginalCount m)
    simpa [hmarginalSum, M] using h
  have hrowDiv (j : Fin 9) :
      (∏ sigma : {sigma : FixedHashSupportTriple // sigma.1 0 = j},
          (fixedHashTargetJointTable m sigma.1).factorial) ∣
        (fixedMarginalCount m j).factorial := by
    have h := Nat.prod_factorial_dvd_factorial_sum
      (Finset.univ : Finset
        {sigma : FixedHashSupportTriple // sigma.1 0 = j})
      (fun sigma ↦ fixedHashTargetJointTable m sigma.1)
    simpa [mme_stothers_fixed_target_joint_table_marginal m 0 j] using h
  have hrowsDiv :
      (∏ j : Fin 9,
        ∏ sigma : {sigma : FixedHashSupportTriple // sigma.1 0 = j},
          (fixedHashTargetJointTable m sigma.1).factorial) ∣ M := by
    apply Finset.prod_dvd_prod_of_dvd
    intro j _
    exact hrowDiv j
  have hrowPartition :
      (∏ j : Fin 9,
        ∏ sigma : {sigma : FixedHashSupportTriple // sigma.1 0 = j},
          (fixedHashTargetJointTable m sigma.1).factorial) = B := by
    calc
      (∏ j : Fin 9,
          ∏ sigma : {sigma : FixedHashSupportTriple // sigma.1 0 = j},
            (fixedHashTargetJointTable m sigma.1).factorial) =
          ∏ x : Sigma fun j : Fin 9 ↦
            {sigma : FixedHashSupportTriple // sigma.1 0 = j},
            (fixedHashTargetJointTable m x.2.1).factorial := by
        exact (Fintype.prod_sigma
          (fun x : Sigma fun j : Fin 9 ↦
            {sigma : FixedHashSupportTriple // sigma.1 0 = j} ↦
            (fixedHashTargetJointTable m x.2.1).factorial)).symm
      _ = ∏ sigma : FixedHashSupportTriple,
          (fixedHashTargetJointTable m sigma).factorial := by
        simpa only using
          (Equiv.prod_comp
            (Equiv.sigmaFiberEquiv
              (fun sigma : FixedHashSupportTriple ↦ sigma.1 0))
            (fun sigma : FixedHashSupportTriple ↦
              (fixedHashTargetJointTable m sigma).factorial))
      _ = B := rfl
  have hBdivM : B ∣ M := by
    rw [← hrowPartition]
    exact hrowsDiv
  have hMpos : 0 < M := by
    exact Finset.prod_pos fun j _ ↦ Nat.factorial_pos _
  have hBpos : 0 < B := by
    exact Finset.prod_pos fun sigma _ ↦ Nat.factorial_pos _
  have hBleM : B ≤ M := Nat.le_of_dvd hMpos hBdivM
  have hDpos : 0 < M / B := Nat.div_pos hBleM hBpos
  have hfactor : (N.factorial / M) * (M / B) = N.factorial / B :=
    Nat.div_mul_div hMdivN hBdivM
  have hTnat :
      Nat.card
          {a : FixedMarginalSupportedAddress m //
            FixedHasExactJointProfile a} =
        N.factorial / B := by
    simpa only [N, B] using
      mme_stothers_fixed_exact_target_subtype_nat_card m
  have hMcastNe : (M : ℝ) ≠ 0 := by
    exact_mod_cast hMpos.ne'
  constructor
  · calc
      (Nat.card
          {a : FixedMarginalSupportedAddress m //
            FixedHasExactJointProfile a} : ℝ) =
          ((N.factorial / B : ℕ) : ℝ) := by rw [hTnat]
      _ = (((N.factorial / M) * (M / B) : ℕ) : ℝ) := by
        rw [hfactor]
      _ = ((N.factorial / M : ℕ) : ℝ) *
          ((M / B : ℕ) : ℝ) := by norm_num
      _ = ((N.factorial : ℝ) / (M : ℝ)) *
          ((M / B : ℕ) : ℝ) := by
        rw [Nat.cast_div hMdivN hMcastNe]
      _ = ((N.factorial : ℝ) / (M : ℝ)) *
          (fixedHashTargetStarDegree m : ℝ) := by
        rfl
  · change 1 ≤ M / B
    omega
