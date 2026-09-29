-- Prove2me | solution 1 for MME.StothersFourth.mme_stothers_fixed_hash_degree_exponential_budget
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T21:32:34.57439+00:00
-- url     : https://prove2.me/submissions/ec7c0179-570f-413c-bc42-20e15966d296

import Mathlib.Data.Fintype.BigOperators
import Definitions.Def_mme_stothers_fixed_outer_profile
import Definitions.Def_mme_stothers_fixed_joint_tables
import Theorems.Thm_mme_stothers_fixed_outer_profile_arithmetic
import Theorems.Thm_MME_StothersFourth_mme_stothers_fixed_exact_target_count_factorization

open MME BigOperators

set_option autoImplicit false
set_option warningAsError true

namespace MME.StothersFourth

private theorem fixedTargetSubtypeCard_le_raw (m : ℕ) :
    Nat.card
        {a : FixedMarginalSupportedAddress m //
          FixedHasExactJointProfile a} ≤
      729 ^ fixedOuterLength m := by
  classical
  letI : Fintype (FixedOuterAddress m) := by
    unfold FixedOuterAddress
    infer_instance
  letI : Fintype (FixedMarginalSupportedAddress m) := by
    unfold FixedMarginalSupportedAddress
    infer_instance
  letI : Fintype
      {a : FixedMarginalSupportedAddress m //
        FixedHasExactJointProfile a} := by
    infer_instance
  rw [Nat.card_eq_fintype_card]
  calc
    Fintype.card
        {a : FixedMarginalSupportedAddress m //
          FixedHasExactJointProfile a} ≤
        Fintype.card (FixedMarginalSupportedAddress m) :=
      Fintype.card_subtype_le _
    _ ≤ Fintype.card (FixedOuterAddress m) :=
      Fintype.card_subtype_le _
    _ = 729 ^ fixedOuterLength m := by
      calc
        Fintype.card (FixedOuterAddress m) =
            Fintype.card
              (Fin 3 → Fin (fixedOuterLength m) → Fin 9) :=
          Fintype.card_congr (Equiv.refl _)
        _ = (9 ^ fixedOuterLength m) ^ 3 := by
          simp only [Fintype.card_fun, Fintype.card_fin]
        _ = 729 ^ fixedOuterLength m := by
          rw [← pow_mul, mul_comm, pow_mul]
          norm_num

private theorem fixedTargetDegree_le_raw (m : ℕ) :
    fixedHashTargetStarDegree m ≤ 729 ^ fixedOuterLength m := by
  classical
  let N := fixedOuterLength m
  let M := ∏ j : Fin 9, (fixedMarginalCount m j).factorial
  let T := Nat.card
    {a : FixedMarginalSupportedAddress m // FixedHasExactJointProfile a}
  have hsum :
      (∑ j : Fin 9, fixedMarginalCount m j) = N := by
    simp only [fixedMarginalCount]
    rw [← Finset.mul_sum,
      mme_stothers_fixed_outer_profile_arithmetic.2.2.2.2.1]
    simp only [N, fixedOuterLength]
    ac_rfl
  have hMdivN : M ∣ N.factorial := by
    have h := Nat.prod_factorial_dvd_factorial_sum
      (Finset.univ : Finset (Fin 9)) (fixedMarginalCount m)
    simpa [hsum, M] using h
  have hMpos : 0 < M :=
    Finset.prod_pos fun j _ ↦ Nat.factorial_pos _
  have hquotPos : 0 < N.factorial / M :=
    Nat.div_pos (Nat.le_of_dvd (Nat.factorial_pos _) hMdivN) hMpos
  have hquotOne : 1 ≤ N.factorial / M := hquotPos
  have hMcast :
      (M : ℝ) =
        ∏ j : Fin 9, ((fixedMarginalCount m j).factorial : ℝ) := by
    simp only [M, Nat.cast_prod]
  have hfactor :=
    mme_stothers_fixed_exact_target_count_factorization m
  dsimp only at hfactor
  rw [← hMcast] at hfactor
  have hcastDiv :
      (((N.factorial / M : ℕ) : ℝ)) =
        (N.factorial : ℝ) / (M : ℝ) := by
    exact Nat.cast_div hMdivN (by exact_mod_cast hMpos.ne')
  have hVone :
      (1 : ℝ) ≤ (N.factorial : ℝ) / (M : ℝ) := by
    rw [← hcastDiv]
    exact_mod_cast hquotOne
  have hDcast :
      (fixedHashTargetStarDegree m : ℝ) ≤ (T : ℝ) := by
    have hnonneg :
        (0 : ℝ) ≤ (fixedHashTargetStarDegree m : ℝ) := by positivity
    dsimp only [T]
    rw [hfactor.1]
    nlinarith
  have hDT : fixedHashTargetStarDegree m ≤ T := by
    exact_mod_cast hDcast
  exact hDT.trans (by
    simpa only [T] using fixedTargetSubtypeCard_le_raw m)

private theorem six_mul_succ_le_five_pow
    (N : ℕ) (hN : 2 ≤ N) :
    6 * (N + 1) ≤ 5 ^ N := by
  induction N, hN using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      calc
        6 * (n + 1 + 1) ≤ 5 * (6 * (n + 1)) := by omega
        _ ≤ 5 * (5 ^ n) := Nat.mul_le_mul_left 5 ih
        _ = 5 ^ (n + 1) := by
          rw [pow_succ]
          omega

end MME.StothersFourth

theorem solution
    (m : ℕ) (hm : 0 < m) :
    let N := MME.StothersFourth.fixedOuterLength m
    (6 * (N + 1)) ^ 100 *
        MME.StothersFourth.fixedHashTargetStarDegree m ≤
      5 ^ (1000 * N) := by
  dsimp only
  let N := MME.StothersFourth.fixedOuterLength m
  have hN : 2 ≤ N := by
    simp only [N, MME.StothersFourth.fixedOuterLength,
      MME.StothersFourth.fixedProfileScale]
    omega
  have hbase : 6 * (N + 1) ≤ 5 ^ N :=
    MME.StothersFourth.six_mul_succ_le_five_pow N hN
  have hpoly :
      (6 * (N + 1)) ^ 100 ≤ 5 ^ (100 * N) := by
    calc
      (6 * (N + 1)) ^ 100 ≤ (5 ^ N) ^ 100 :=
        Nat.pow_le_pow_left hbase 100
      _ = 5 ^ (N * 100) := by rw [pow_mul]
      _ = 5 ^ (100 * N) := by rw [mul_comm]
  have hdegree :
      MME.StothersFourth.fixedHashTargetStarDegree m ≤ 729 ^ N := by
    simpa only [N] using
      MME.StothersFourth.fixedTargetDegree_le_raw m
  have h729 : 729 ^ N ≤ 5 ^ (5 * N) := by
    calc
      729 ^ N ≤ (5 ^ 5) ^ N :=
        Nat.pow_le_pow_left (by norm_num) N
      _ = 5 ^ (5 * N) := by rw [pow_mul]
  calc
    (6 * (N + 1)) ^ 100 *
          MME.StothersFourth.fixedHashTargetStarDegree m ≤
        (6 * (N + 1)) ^ 100 * (729 ^ N) :=
      Nat.mul_le_mul_left _ hdegree
    _ ≤ 5 ^ (100 * N) * 5 ^ (5 * N) :=
      Nat.mul_le_mul hpoly h729
    _ = 5 ^ (105 * N) := by
      rw [← pow_add]
      congr 2
      omega
    _ ≤ 5 ^ (1000 * N) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
