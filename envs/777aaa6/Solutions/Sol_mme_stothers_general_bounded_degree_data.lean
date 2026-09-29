-- Prove2me | solution 1 for mme_stothers_general_bounded_degree_data
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-09-09T02:59:19.25488+00:00
-- url     : https://prove2.me/submissions/040ccbe3-e9af-4735-8779-dc967f1ab957

import Mathlib.Data.Fintype.BigOperators
import Definitions.Def_mme_stothers_general_outer_profile
import Definitions.Def_mme_modern_entropy_data
import Theorems.Thm_mme_stothers_general_outer_profile_arithmetic
import Theorems.Thm_mme_stothers_general_exact_target_count_factorization
import Theorems.Thm_mme_stothers_general_completion_quotient_le_polynomial_target
import Theorems.Thm_mme_stothers_general_exact_target_star_degree_le_power100

open MME BigOperators Filter

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

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



private theorem genScale_eq_of_same_marginals
    (base bstar : Fin 10 → ℕ)
    (hsame : ∀ j, genMarginalBaseCount bstar j = genMarginalBaseCount base j) :
    genProfileScale bstar = genProfileScale base := by
  have h1 := mme_stothers_general_outer_profile_arithmetic.2.1 bstar
  have h2 := mme_stothers_general_outer_profile_arithmetic.2.1 base
  have h3 : ∑ j : Fin 9, genMarginalBaseCount bstar j =
      ∑ j : Fin 9, genMarginalBaseCount base j :=
    Finset.sum_congr rfl (fun j _ ↦ hsame j)
  omega

private theorem genLength_eq_of_same_marginals
    (base bstar : Fin 10 → ℕ) (m : ℕ)
    (hsame : ∀ j, genMarginalBaseCount bstar j = genMarginalBaseCount base j) :
    genOuterLength bstar m = genOuterLength base m := by
  simp only [genOuterLength, genScale_eq_of_same_marginals base bstar hsame]

private theorem genPoly200_budget (base : Fin 10 → ℕ) (m : ℕ) (hm : 0 < m)
    (hbase : ∀ r, 0 < base r) :
    (6 * (genOuterLength base m + 1)) ^ 200 *
        genHashTargetStarDegree base m ≤
      5 ^ (1000 * genOuterLength base m) := by
  set N := genOuterLength base m with hNdef
  have hscale : 0 < genProfileScale base := by
    refine Finset.sum_pos' (fun i _ ↦ Nat.zero_le _)
      ⟨0, Finset.mem_univ 0, ?_⟩
    have h0 := hbase 0
    simpa [classMultiplicity] using h0
  have hN : 2 ≤ N := by
    have hpos : 0 < genProfileScale base * m := Nat.mul_pos hscale hm
    simp only [hNdef, genOuterLength]
    omega
  have hfive : 6 * (N + 1) ≤ 5 ^ N := genSix_mul_succ_le_five_pow N hN
  have hpoly : (6 * (N + 1)) ^ 200 ≤ 5 ^ (200 * N) := by
    calc
      (6 * (N + 1)) ^ 200 ≤ (5 ^ N) ^ 200 := Nat.pow_le_pow_left hfive 200
      _ = 5 ^ (N * 200) := by rw [← pow_mul]
      _ = 5 ^ (200 * N) := by rw [mul_comm]
  have hdegree : genHashTargetStarDegree base m ≤ 729 ^ N :=
    genTargetDegree_le_raw base m
  have h729 : (729 : ℕ) ^ N ≤ 5 ^ (5 * N) := by
    calc
      729 ^ N ≤ (5 ^ 5) ^ N := Nat.pow_le_pow_left (by norm_num) N
      _ = 5 ^ (5 * N) := by rw [pow_mul]
  calc
    (6 * (N + 1)) ^ 200 * genHashTargetStarDegree base m ≤
        (6 * (N + 1)) ^ 200 * 729 ^ N := Nat.mul_le_mul_left _ hdegree
    _ ≤ 5 ^ (200 * N) * 5 ^ (5 * N) := Nat.mul_le_mul hpoly h729
    _ = 5 ^ (205 * N) := by
      rw [← pow_add]
      congr 2
      omega
    _ ≤ 5 ^ (1000 * N) := Nat.pow_le_pow_right (by norm_num) (by omega)

end MME.StothersFourth

open MME.StothersFourth

theorem solution
    (base bstar : Fin 10 → ℕ)
    (hbase : ∀ r, 0 < base r) (hbstar : ∀ r, 0 < bstar r)
    (hsame : ∀ j, genMarginalBaseCount bstar j = genMarginalBaseCount base j)
    (hcond : ∀ (m : ℕ) (k : GenHashJointMultiplicityTable),
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
              (genMarginalCount base m j : ℝ))) :
    ∀ᶠ m : ℕ in atTop,
      let N := genOuterLength base m
      let V : ℝ :=
        (N.factorial : ℝ) /
          ∏ j : Fin 9, ((genMarginalCount base m j).factorial : ℝ)
      (Nat.card
          {a : GenMarginalSupportedAddress base m //
            GenHasExactJointProfile a} : ℝ) =
          V * (genHashTargetStarDegree base m : ℝ) ∧
        1 ≤ genHashTargetStarDegree base m ∧
        genHashTargetStarDegree base m ≤
          (6 * (N + 1)) ^ 100 * genHashTargetStarDegree bstar m ∧
        (∀ i : Fin 3,
          ∀ a : {a : GenMarginalSupportedAddress base m //
            GenHasExactJointProfile a},
          Nat.card
            {b : GenMarginalSupportedAddress base m //
              b.1 i = a.1.1 i} ≤
            (6 * (N + 1)) ^ 100 *
              ((6 * (N + 1)) ^ 100 * genHashTargetStarDegree bstar m)) ∧
        (6 * (N + 1)) ^ 100 *
            ((6 * (N + 1)) ^ 100 * genHashTargetStarDegree bstar m) ≤
          5 ^ (1000 * N) := by
  filter_upwards [eventually_gt_atTop 0] with m hm
  dsimp only
  set N := genOuterLength base m with hNdef
  have hNeq : genOuterLength bstar m = N :=
    genLength_eq_of_same_marginals base bstar m hsame
  have hPpos : 0 < (6 * (N + 1)) ^ 100 := by positivity
  have hone : 1 ≤ (6 * (N + 1)) ^ 100 := hPpos
  have hfactor :=
    mme_stothers_general_exact_target_count_factorization base m
  dsimp only at hfactor
  refine ⟨hfactor.1, hfactor.2, ?_, ?_, ?_⟩
  · -- Dstar(base) <= (6(N+1))^100 * Dstar(bstar)
    have hkMarg : ∀ l : Fin 3, ∀ j : Fin 9,
        (∑ sigma : {sigma : GenHashSupportTriple // sigma.1 l = j},
          genHashTargetJointTable base m sigma.1) =
          genMarginalCount base m j := by
      intro l j
      exact mme_stothers_general_outer_profile_arithmetic.2.2.2 base m l j
    have hq :=
      mme_stothers_general_completion_quotient_le_polynomial_target
        base bstar m hm hbase hsame (0 : Fin 3)
        (genHashTargetJointTable base m) hkMarg
        (hcond m (genHashTargetJointTable base m) hkMarg (0 : Fin 3))
    have hqNat :
        genHashTargetStarDegree base m ≤
          (6 * (N + 1)) ^ 45 * genHashTargetStarDegree bstar m := by
      apply (Nat.cast_le (α := ℝ)).mp
      have hstar : genHashTargetStarDegree base m =
          (∏ j : Fin 9, (genMarginalCount base m j).factorial) /
            ∏ sigma : GenHashSupportTriple,
              (genHashTargetJointTable base m sigma).factorial := rfl
      rw [hstar]
      simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one,
        Nat.cast_ofNat, hNdef] using hq
    refine hqNat.trans ?_
    exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) (by omega))
  · intro i a
    refine (mme_stothers_general_exact_target_star_degree_le_power100
      base bstar m hm hbase hsame (hcond m) i a).trans ?_
    exact Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ hPpos)
  · have h200 : (6 * (N + 1)) ^ 200 * genHashTargetStarDegree bstar m ≤
        5 ^ (1000 * N) := by
      have := genPoly200_budget bstar m hm hbstar
      rw [hNeq] at this
      exact this
    calc
      (6 * (N + 1)) ^ 100 *
          ((6 * (N + 1)) ^ 100 * genHashTargetStarDegree bstar m) =
          (6 * (N + 1)) ^ 200 * genHashTargetStarDegree bstar m := by
        rw [← mul_assoc, ← pow_add]
      _ ≤ 5 ^ (1000 * N) := h200
