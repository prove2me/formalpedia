-- Prove2me | solution 1 for mme_CW_2376_exact_target_count_factorization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T23:36:06.111221+00:00
-- url     : https://prove2.me/submissions/7ee8e3f8-2c9d-4a96-b237-1e4f7aa27504

import Definitions.Def_mme_CW_2376_marginal_joint_tables
import Theorems.Thm_mme_CW_2376_exact_profile_address_nat_card
import Theorems.Thm_mme_CW_2376_all_exact_target_edges_card
import Theorems.Thm_mme_CW_2376_target_joint_table_marginal

open MME BigOperators

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

/-- The target count is the number of mode words times the exact target
completion degree, and that completion degree is positive. -/
theorem solution (m : ℕ) :
    let N := cw2376ProfileLength m
    let V : ℝ :=
      (N.factorial : ℝ) /
        (∏ r : Fin 5, ((cw2376MarginalMultiplicity m r).factorial : ℝ))
    ((cw2376AllExactTargetEdges m).card : ℝ) =
        V * (cw2376TargetStarDegree m : ℝ) ∧
      1 ≤ cw2376TargetStarDegree m := by
  dsimp only
  classical
  let N := cw2376ProfileLength m
  let M := ∏ r : Fin 5, (cw2376MarginalMultiplicity m r).factorial
  let B := ∏ sigma : CW2376SupportedJointType,
    (cw2376TargetJointTable m sigma).factorial
  have hMcast : (M : ℝ) =
      ∏ r : Fin 5,
        ((cw2376MarginalMultiplicity m r).factorial : ℝ) := by
    simp only [M, Nat.cast_prod]
  rw [← hMcast]
  change ((cw2376AllExactTargetEdges m).card : ℝ) =
      ((N.factorial : ℝ) / (M : ℝ)) *
        (cw2376TargetStarDegree m : ℝ) ∧
    1 ≤ cw2376TargetStarDegree m

  have hmarginalSum :
      (∑ r : Fin 5, cw2376MarginalMultiplicity m r) = N := by
    simp [N, cw2376ProfileLength, cw2376MarginalMultiplicity,
      Fin.sum_univ_succ]
    omega
  have hMdivN : M ∣ N.factorial := by
    have h := Nat.prod_factorial_dvd_factorial_sum
      (Finset.univ : Finset (Fin 5))
      (cw2376MarginalMultiplicity m)
    simpa [hmarginalSum, M] using h
  have hrowDiv (r : Fin 5) :
      (∏ sigma : {sigma : CW2376SupportedJointType // sigma.1 0 = r},
          (cw2376TargetJointTable m sigma.1).factorial) ∣
        (cw2376MarginalMultiplicity m r).factorial := by
    have h := Nat.prod_factorial_dvd_factorial_sum
      (Finset.univ : Finset
        {sigma : CW2376SupportedJointType // sigma.1 0 = r})
      (fun sigma => cw2376TargetJointTable m sigma.1)
    simpa [mme_CW_2376_target_joint_table_marginal m 0 r] using h
  have hrowsDiv :
      (∏ r : Fin 5,
        ∏ sigma : {sigma : CW2376SupportedJointType // sigma.1 0 = r},
          (cw2376TargetJointTable m sigma.1).factorial) ∣ M := by
    apply Finset.prod_dvd_prod_of_dvd
    intro r hr
    exact hrowDiv r
  have hrowPartition :
      (∏ r : Fin 5,
        ∏ sigma : {sigma : CW2376SupportedJointType // sigma.1 0 = r},
          (cw2376TargetJointTable m sigma.1).factorial) = B := by
    calc
      (∏ r : Fin 5,
          ∏ sigma : {sigma : CW2376SupportedJointType // sigma.1 0 = r},
            (cw2376TargetJointTable m sigma.1).factorial) =
          ∏ x : Σ r : Fin 5,
            {sigma : CW2376SupportedJointType // sigma.1 0 = r},
            (cw2376TargetJointTable m x.2.1).factorial := by
        exact (Fintype.prod_sigma
          (fun x : Σ r : Fin 5,
            {sigma : CW2376SupportedJointType // sigma.1 0 = r} =>
            (cw2376TargetJointTable m x.2.1).factorial)).symm
      _ = ∏ sigma : CW2376SupportedJointType,
          (cw2376TargetJointTable m sigma).factorial := by
        simpa only using
          (Equiv.prod_comp
            (Equiv.sigmaFiberEquiv
              (fun sigma : CW2376SupportedJointType => sigma.1 0))
            (fun sigma : CW2376SupportedJointType =>
              (cw2376TargetJointTable m sigma).factorial))
      _ = B := rfl
  have hBdivM : B ∣ M := by
    rw [← hrowPartition]
    exact hrowsDiv
  have hMpos : 0 < M := by
    exact Finset.prod_pos fun r hr => Nat.factorial_pos _
  have hBpos : 0 < B := by
    exact Finset.prod_pos fun sigma hsigma => Nat.factorial_pos _
  have hBleM : B ≤ M := Nat.le_of_dvd hMpos hBdivM
  have hDpos : 0 < M / B := Nat.div_pos hBleM hBpos
  have hfactor : (N.factorial / M) * (M / B) = N.factorial / B :=
    Nat.div_mul_div hMdivN hBdivM
  have hTnat : (cw2376AllExactTargetEdges m).card = N.factorial / B := by
    rw [mme_CW_2376_all_exact_target_edges_card,
      mme_CW_2376_exact_profile_address_nat_card]
  have hMcastNe : (M : ℝ) ≠ 0 := by exact_mod_cast hMpos.ne'
  constructor
  · calc
      ((cw2376AllExactTargetEdges m).card : ℝ) =
          ((N.factorial / B : ℕ) : ℝ) := by rw [hTnat]
      _ = (((N.factorial / M) * (M / B) : ℕ) : ℝ) := by
        rw [hfactor]
      _ = ((N.factorial / M : ℕ) : ℝ) *
          ((M / B : ℕ) : ℝ) := by norm_num
      _ = ((N.factorial : ℝ) / (M : ℝ)) *
          ((M / B : ℕ) : ℝ) := by
        rw [Nat.cast_div hMdivN hMcastNe]
      _ = ((N.factorial : ℝ) / (M : ℝ)) *
          (cw2376TargetStarDegree m : ℝ) := by
        rfl
  · change 1 ≤ M / B
    omega
