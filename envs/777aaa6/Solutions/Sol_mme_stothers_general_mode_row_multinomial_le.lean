-- Prove2me | solution 1 for mme_stothers_general_mode_row_multinomial_le
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-09-08T05:31:18.202042+00:00
-- url     : https://prove2.me/submissions/c0eef981-2012-4ca2-b14a-99483d2ff3eb

import Definitions.Def_mme_stothers_general_outer_profile
import Definitions.Def_mme_modern_entropy_data
import Theorems.Thm_mme_stothers_general_outer_profile_arithmetic
import Theorems.Thm_mme_dwz_multinomial_entropy_upper
import Theorems.Thm_mme_dwz_multinomial_entropy_polynomial_lower

open MME BigOperators

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

namespace MME.StothersFourth

private theorem rowMarginalSum (base : Fin 10 → ℕ) (m : ℕ) :
    ∑ j : Fin 9, genMarginalCount base m j = genOuterLength base m := by
  simp only [genMarginalCount]
  rw [← Finset.sum_mul,
    mme_stothers_general_outer_profile_arithmetic.2.1 base]
  simp only [genOuterLength]
  ac_rfl

private theorem rowMarginalBasePos (base : Fin 10 → ℕ)
    (hbase : ∀ r, 0 < base r) (j : Fin 9) :
    0 < genMarginalBaseCount base j := by
  have n0 := hbase 0
  have n1 := hbase 1
  have n2 := hbase 2
  have n3 := hbase 3
  have n4 := hbase 4
  have n5 := hbase 5
  have n6 := hbase 6
  have n7 := hbase 7
  have n8 := hbase 8
  have n9 := hbase 9
  fin_cases j <;>
    simp [genMarginalBaseCount, genClassMarginalMultiplicity,
      Fin.sum_univ_succ] <;> omega

private theorem rowMarginalPos (base : Fin 10 → ℕ) (m : ℕ) (hm : 0 < m)
    (hbase : ∀ r, 0 < base r) (j : Fin 9) :
    0 < genMarginalCount base m j := by
  exact Nat.mul_pos (rowMarginalBasePos base hbase j) hm

private theorem rowMarginalLe (base : Fin 10 → ℕ) (m : ℕ) (j : Fin 9) :
    genMarginalCount base m j ≤ genOuterLength base m := by
  rw [← rowMarginalSum base m]
  exact Finset.single_le_sum (fun r _ ↦ Nat.zero_le _) (Finset.mem_univ j)

private theorem targetRowMarginal (base bstar : Fin 10 → ℕ) (m : ℕ)
    (hsame : ∀ j, genMarginalBaseCount bstar j = genMarginalBaseCount base j)
    (i : Fin 3) (j : Fin 9) :
    (∑ sigma : {sigma : GenHashSupportTriple // sigma.1 i = j},
      genHashTargetJointTable bstar m sigma.1) = genMarginalCount base m j := by
  rw [mme_stothers_general_outer_profile_arithmetic.2.2.2 bstar m i j]
  simp only [genMarginalCount, hsame j]

private theorem rowCardSum (i : Fin 3) :
    ∑ j : Fin 9,
        Fintype.card {sigma : GenHashSupportTriple // sigma.1 i = j} = 45 := by
  calc
    (∑ j : Fin 9,
        Fintype.card {sigma : GenHashSupportTriple // sigma.1 i = j}) =
        Fintype.card
          (Sigma fun j : Fin 9 ↦
            {sigma : GenHashSupportTriple // sigma.1 i = j}) :=
      (Fintype.card_sigma).symm
    _ = Fintype.card GenHashSupportTriple :=
      Fintype.card_congr
        (Equiv.sigmaFiberEquiv
          (fun sigma : GenHashSupportTriple ↦ sigma.1 i))
    _ = 45 := by decide

end MME.StothersFourth

open MME.StothersFourth

theorem solution
    (base bstar : Fin 10 → ℕ) (m : ℕ) (hm : 0 < m)
    (hbase : ∀ r, 0 < base r)
    (hsame : ∀ j, genMarginalBaseCount bstar j = genMarginalBaseCount base j)
    (i : Fin 3)
    (k : GenHashJointMultiplicityTable)
    (hkMarginal : ∀ l : Fin 3, ∀ j : Fin 9,
      (∑ sigma : {sigma : GenHashSupportTriple // sigma.1 l = j},
        k sigma.1) = genMarginalCount base m j)
    (hcond :
      (∑ j : Fin 9, (genMarginalCount base m j : ℝ) *
        mme_modern_entropyBits
          (fun sigma : {sigma : GenHashSupportTriple // sigma.1 i = j} ↦
            (k sigma.1 : ℝ) / (genMarginalCount base m j : ℝ))) ≤
      ∑ j : Fin 9, (genMarginalCount base m j : ℝ) *
        mme_modern_entropyBits
          (fun sigma : {sigma : GenHashSupportTriple // sigma.1 i = j} ↦
            (genHashTargetJointTable bstar m sigma.1 : ℝ) /
              (genMarginalCount base m j : ℝ))) :
    (∏ j : Fin 9,
        (Nat.multinomial Finset.univ
          (fun sigma : {sigma : GenHashSupportTriple // sigma.1 i = j} ↦
            k sigma.1) : ℝ)) ≤
      (6 * (((genOuterLength base m + 1 : ℕ) : ℝ))) ^ 45 *
        ∏ j : Fin 9,
          (Nat.multinomial Finset.univ
            (fun sigma : {sigma : GenHashSupportTriple // sigma.1 i = j} ↦
              genHashTargetJointTable bstar m sigma.1) : ℝ) := by
  classical
  let candidateExponent : Fin 9 → ℝ := fun j ↦
    (genMarginalCount base m j : ℝ) * Real.log 2 *
      mme_modern_entropyBits
        (fun sigma : {sigma : GenHashSupportTriple // sigma.1 i = j} ↦
          (k sigma.1 : ℝ) / (genMarginalCount base m j : ℝ))
  let targetExponent : Fin 9 → ℝ := fun j ↦
    (genMarginalCount base m j : ℝ) * Real.log 2 *
      mme_modern_entropyBits
        (fun sigma : {sigma : GenHashSupportTriple // sigma.1 i = j} ↦
          (genHashTargetJointTable bstar m sigma.1 : ℝ) /
            (genMarginalCount base m j : ℝ))
  let rowPolynomial : Fin 9 → ℝ := fun j ↦
    (6 * (((genMarginalCount base m j + 1 : ℕ) : ℝ))) ^
      Fintype.card {sigma : GenHashSupportTriple // sigma.1 i = j}
  have hcandidateUpper (j : Fin 9) :
      (Nat.multinomial Finset.univ
          (fun sigma : {sigma : GenHashSupportTriple // sigma.1 i = j} ↦
            k sigma.1) : ℝ) ≤
        Real.exp (candidateExponent j) := by
    have hrowPos :
        0 < ∑ sigma :
          {sigma : GenHashSupportTriple // sigma.1 i = j},
            k sigma.1 := by
      rw [hkMarginal i j]
      exact rowMarginalPos base m hm hbase j
    have h := mme_dwz_multinomial_entropy_upper
      (fun sigma : {sigma : GenHashSupportTriple // sigma.1 i = j} ↦
        k sigma.1) 1 (by decide) hrowPos
    rw [hkMarginal i j] at h
    simpa only [Nat.mul_one, Nat.cast_one, one_mul, candidateExponent] using h
  have htargetLower (j : Fin 9) :
      Real.exp (targetExponent j) ≤
        rowPolynomial j *
          (Nat.multinomial Finset.univ
            (fun sigma : {sigma : GenHashSupportTriple // sigma.1 i = j} ↦
              genHashTargetJointTable bstar m sigma.1) : ℝ) := by
    have hrowPos :
        0 < ∑ sigma :
          {sigma : GenHashSupportTriple // sigma.1 i = j},
            genHashTargetJointTable bstar m sigma.1 := by
      rw [targetRowMarginal base bstar m hsame i j]
      exact rowMarginalPos base m hm hbase j
    have h := mme_dwz_multinomial_entropy_polynomial_lower
      (fun sigma : {sigma : GenHashSupportTriple // sigma.1 i = j} ↦
        genHashTargetJointTable bstar m sigma.1) 1 (by decide) hrowPos
    rw [targetRowMarginal base bstar m hsame i j] at h
    simpa only [Nat.mul_one, Nat.cast_one, one_mul, targetExponent,
      rowPolynomial] using h
  have hconditional := hcond
  have hlogNonneg : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hconditionalLog :=
    mul_le_mul_of_nonneg_right hconditional hlogNonneg
  have hcandidateExponentSum :
      (∑ j : Fin 9,
        (genMarginalCount base m j : ℝ) *
          mme_modern_entropyBits
            (fun sigma :
              {sigma : GenHashSupportTriple // sigma.1 i = j} ↦
                (k sigma.1 : ℝ) /
                  (genMarginalCount base m j : ℝ))) * Real.log 2 =
        ∑ j, candidateExponent j := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [candidateExponent]
    ring
  have htargetExponentSum :
      (∑ j : Fin 9,
        (genMarginalCount base m j : ℝ) *
          mme_modern_entropyBits
            (fun sigma :
              {sigma : GenHashSupportTriple // sigma.1 i = j} ↦
                (genHashTargetJointTable bstar m sigma.1 : ℝ) /
                  (genMarginalCount base m j : ℝ))) * Real.log 2 =
        ∑ j, targetExponent j := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [targetExponent]
    ring
  rw [hcandidateExponentSum, htargetExponentSum] at hconditionalLog
  have hproductCandidate :
      (∏ j : Fin 9,
          (Nat.multinomial Finset.univ
            (fun sigma :
              {sigma : GenHashSupportTriple // sigma.1 i = j} ↦
                k sigma.1) : ℝ)) ≤
        Real.exp (∑ j, candidateExponent j) := by
    calc
      (∏ j : Fin 9,
          (Nat.multinomial Finset.univ
            (fun sigma :
              {sigma : GenHashSupportTriple // sigma.1 i = j} ↦
                k sigma.1) : ℝ)) ≤
          ∏ j : Fin 9, Real.exp (candidateExponent j) := by
        apply Finset.prod_le_prod
        · intro j _
          positivity
        · intro j _
          exact hcandidateUpper j
      _ = Real.exp (∑ j, candidateExponent j) :=
        (Real.exp_sum Finset.univ candidateExponent).symm
  have hproductTarget :
      Real.exp (∑ j, targetExponent j) ≤
        ∏ j : Fin 9,
          rowPolynomial j *
            (Nat.multinomial Finset.univ
              (fun sigma :
                {sigma : GenHashSupportTriple // sigma.1 i = j} ↦
                  genHashTargetJointTable bstar m sigma.1) : ℝ) := by
    rw [Real.exp_sum]
    apply Finset.prod_le_prod
    · intro j _
      positivity
    · intro j _
      exact htargetLower j
  have hrowPolynomial (j : Fin 9) :
      rowPolynomial j ≤
        (6 * (((genOuterLength base m + 1 : ℕ) : ℝ))) ^
          Fintype.card
            {sigma : GenHashSupportTriple // sigma.1 i = j} := by
    dsimp only [rowPolynomial]
    gcongr
    exact_mod_cast rowMarginalLe base m j
  have hpolynomialProduct :
      (∏ j : Fin 9, rowPolynomial j) ≤
        (6 * (((genOuterLength base m + 1 : ℕ) : ℝ))) ^ 45 := by
    calc
      (∏ j : Fin 9, rowPolynomial j) ≤
          ∏ j : Fin 9,
            (6 * (((genOuterLength base m + 1 : ℕ) : ℝ))) ^
              Fintype.card
                {sigma : GenHashSupportTriple // sigma.1 i = j} := by
        apply Finset.prod_le_prod
        · intro j _
          positivity
        · intro j _
          exact hrowPolynomial j
      _ = (6 * (((genOuterLength base m + 1 : ℕ) : ℝ))) ^
          (∑ j : Fin 9,
            Fintype.card
              {sigma : GenHashSupportTriple // sigma.1 i = j}) := by
        exact Finset.prod_pow_eq_pow_sum _ _ _
      _ = (6 * (((genOuterLength base m + 1 : ℕ) : ℝ))) ^ 45 := by
        rw [rowCardSum i]
  calc
    (∏ j : Fin 9,
        (Nat.multinomial Finset.univ
          (fun sigma : {sigma : GenHashSupportTriple // sigma.1 i = j} ↦
            k sigma.1) : ℝ)) ≤
        Real.exp (∑ j, candidateExponent j) := hproductCandidate
    _ ≤ Real.exp (∑ j, targetExponent j) :=
      Real.exp_le_exp.mpr hconditionalLog
    _ ≤ ∏ j : Fin 9,
        rowPolynomial j *
          (Nat.multinomial Finset.univ
            (fun sigma :
              {sigma : GenHashSupportTriple // sigma.1 i = j} ↦
                genHashTargetJointTable bstar m sigma.1) : ℝ) := hproductTarget
    _ = (∏ j : Fin 9, rowPolynomial j) *
        ∏ j : Fin 9,
          (Nat.multinomial Finset.univ
            (fun sigma :
              {sigma : GenHashSupportTriple // sigma.1 i = j} ↦
                genHashTargetJointTable bstar m sigma.1) : ℝ) := by
      rw [Finset.prod_mul_distrib]
    _ ≤ (6 * (((genOuterLength base m + 1 : ℕ) : ℝ))) ^ 45 *
        ∏ j : Fin 9,
          (Nat.multinomial Finset.univ
            (fun sigma :
              {sigma : GenHashSupportTriple // sigma.1 i = j} ↦
                genHashTargetJointTable bstar m sigma.1) : ℝ) := by
      exact mul_le_mul_of_nonneg_right hpolynomialProduct (by positivity)

