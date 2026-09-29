-- Prove2me | solution 1 for mme_stothers_general_hash_degree_exponential_budget
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-09-08T05:41:14.939671+00:00
-- url     : https://prove2.me/submissions/5d93e696-eb73-47a2-b52c-40317423ad23

import Mathlib.Data.Fintype.BigOperators
import Definitions.Def_mme_stothers_general_outer_profile
import Theorems.Thm_mme_stothers_general_outer_profile_arithmetic
import Theorems.Thm_mme_stothers_general_exact_target_count_factorization

open MME BigOperators

set_option autoImplicit false
set_option warningAsError true

namespace MME.StothersFourth

private theorem genTargetSubtypeCard_le_raw (base : Fin 10 → ℕ) (m : ℕ) :
    Nat.card
        {a : GenMarginalSupportedAddress base m //
          GenHasExactJointProfile a} ≤
      729 ^ genOuterLength base m := by
  classical
  letI : Fintype (GenOuterAddress base m) :=
    inferInstanceAs (Fintype (Fin 3 → Fin (genOuterLength base m) → Fin 9))
  letI : Fintype (GenMarginalSupportedAddress base m) :=
    inferInstanceAs (Fintype
      {b : GenOuterAddress base m //
        GenCoordinatewiseSupported b ∧ GenMarginallyRegular b})
  letI : Fintype
      {a : GenMarginalSupportedAddress base m //
        GenHasExactJointProfile a} := by
    infer_instance
  rw [Nat.card_eq_fintype_card]
  calc
    Fintype.card
        {a : GenMarginalSupportedAddress base m //
          GenHasExactJointProfile a} ≤
        Fintype.card (GenMarginalSupportedAddress base m) :=
      Fintype.card_subtype_le _
    _ ≤ Fintype.card (GenOuterAddress base m) :=
      Fintype.card_subtype_le _
    _ = 729 ^ genOuterLength base m := by
      calc
        Fintype.card (GenOuterAddress base m) =
            Fintype.card
              (Fin 3 → Fin (genOuterLength base m) → Fin 9) :=
          Fintype.card_congr (Equiv.refl _)
        _ = (9 ^ genOuterLength base m) ^ 3 := by
          simp only [Fintype.card_fun, Fintype.card_fin]
        _ = 729 ^ genOuterLength base m := by
          rw [← pow_mul, mul_comm, pow_mul]
          norm_num

private theorem genTargetDegree_le_raw (base : Fin 10 → ℕ) (m : ℕ) :
    genHashTargetStarDegree base m ≤ 729 ^ genOuterLength base m := by
  classical
  let N := genOuterLength base m
  let M := ∏ j : Fin 9, (genMarginalCount base m j).factorial
  let T := Nat.card
    {a : GenMarginalSupportedAddress base m // GenHasExactJointProfile a}
  have hsum :
      (∑ j : Fin 9, genMarginalCount base m j) = N := by
    simp only [genMarginalCount]
    rw [← Finset.sum_mul,
      mme_stothers_general_outer_profile_arithmetic.2.1 base]
    simp only [N, genOuterLength]
    ac_rfl
  have hMdivN : M ∣ N.factorial := by
    have h := Nat.prod_factorial_dvd_factorial_sum
      (Finset.univ : Finset (Fin 9)) (genMarginalCount base m)
    simpa [hsum, M] using h
  have hMpos : 0 < M :=
    Finset.prod_pos fun j _ ↦ Nat.factorial_pos _
  have hquotPos : 0 < N.factorial / M :=
    Nat.div_pos (Nat.le_of_dvd (Nat.factorial_pos _) hMdivN) hMpos
  have hquotOne : 1 ≤ N.factorial / M := hquotPos
  have hMcast :
      (M : ℝ) =
        ∏ j : Fin 9, ((genMarginalCount base m j).factorial : ℝ) := by
    simp only [M, Nat.cast_prod]
  have hfactor :=
    mme_stothers_general_exact_target_count_factorization base m
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
      (genHashTargetStarDegree base m : ℝ) ≤ (T : ℝ) := by
    have hnonneg :
        (0 : ℝ) ≤ (genHashTargetStarDegree base m : ℝ) := by positivity
    dsimp only [T]
    rw [hfactor.1]
    nlinarith
  have hDT : genHashTargetStarDegree base m ≤ T := by
    exact_mod_cast hDcast
  exact hDT.trans (by
    simpa only [T] using genTargetSubtypeCard_le_raw base m)

private theorem genSix_mul_succ_le_five_pow
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
    (base : Fin 10 → ℕ) (m : ℕ) (hm : 0 < m)
    (hbase : ∀ r, 0 < base r) :
    let N := MME.StothersFourth.genOuterLength base m
    (6 * (N + 1)) ^ 100 *
        MME.StothersFourth.genHashTargetStarDegree base m ≤
      5 ^ (1000 * N) := by
  dsimp only
  let N := MME.StothersFourth.genOuterLength base m
  have hscale : 0 < MME.StothersFourth.genProfileScale base := by
    refine Finset.sum_pos' (fun i _ ↦ Nat.zero_le _)
      ⟨0, Finset.mem_univ 0, ?_⟩
    have h0 := hbase 0
    simpa [MME.StothersFourth.classMultiplicity] using h0
  have hN : 2 ≤ N := by
    have hpos : 0 < MME.StothersFourth.genProfileScale base * m :=
      Nat.mul_pos hscale hm
    simp only [N, MME.StothersFourth.genOuterLength]
    omega
  have hfive : 6 * (N + 1) ≤ 5 ^ N :=
    MME.StothersFourth.genSix_mul_succ_le_five_pow N hN
  have hpoly :
      (6 * (N + 1)) ^ 100 ≤ 5 ^ (100 * N) := by
    calc
      (6 * (N + 1)) ^ 100 ≤ (5 ^ N) ^ 100 :=
        Nat.pow_le_pow_left hfive 100
      _ = 5 ^ (N * 100) := by rw [pow_mul]
      _ = 5 ^ (100 * N) := by rw [mul_comm]
  have hdegree :
      MME.StothersFourth.genHashTargetStarDegree base m ≤ 729 ^ N := by
    simpa only [N] using
      MME.StothersFourth.genTargetDegree_le_raw base m
  have h729 : 729 ^ N ≤ 5 ^ (5 * N) := by
    calc
      729 ^ N ≤ (5 ^ 5) ^ N :=
        Nat.pow_le_pow_left (by norm_num) N
      _ = 5 ^ (5 * N) := by rw [pow_mul]
  calc
    (6 * (N + 1)) ^ 100 *
          MME.StothersFourth.genHashTargetStarDegree base m ≤
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

