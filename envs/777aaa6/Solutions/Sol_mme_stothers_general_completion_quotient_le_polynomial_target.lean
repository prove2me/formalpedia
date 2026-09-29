-- Prove2me | solution 1 for mme_stothers_general_completion_quotient_le_polynomial_target
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-09-08T05:32:17.606321+00:00
-- url     : https://prove2.me/submissions/2b35e3b6-d962-435a-8216-4222a761c868

import Definitions.Def_mme_stothers_general_outer_profile
import Definitions.Def_mme_modern_entropy_data
import Theorems.Thm_mme_stothers_general_outer_profile_arithmetic
import Theorems.Thm_mme_stothers_general_mode_row_multinomial_le

open MME BigOperators

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000

namespace MME.StothersFourth

private theorem genHashCompletion_prod_nat_div_eq_div_prod_of_dvd
    {iota : Type*} (s : Finset iota) (A B : iota → ℕ)
    (hdiv : ∀ i ∈ s, B i ∣ A i) :
    (∏ i ∈ s, A i / B i) =
      (∏ i ∈ s, A i) / ∏ i ∈ s, B i := by
  classical
  induction s using Finset.cons_induction_on with
  | empty => simp
  | cons a s ha ih =>
      have haDiv : B a ∣ A a := hdiv a (by simp)
      have hsDiv : ∀ i ∈ s, B i ∣ A i := by
        intro i hi
        exact hdiv i (by simp [hi])
      have hprodDiv : (∏ i ∈ s, B i) ∣ ∏ i ∈ s, A i :=
        Finset.prod_dvd_prod_of_dvd _ _ hsDiv
      simp only [Finset.prod_cons]
      rw [ih hsDiv, Nat.div_mul_div_comm haDiv hprodDiv]

private theorem genHashCompletion_prod_over_coordinate
    (i : Fin 3) (f : GenHashSupportTriple → ℕ) :
    (∏ j : Fin 9,
      ∏ sigma : {sigma : GenHashSupportTriple // sigma.1 i = j},
        f sigma.1) = ∏ sigma : GenHashSupportTriple, f sigma := by
  classical
  calc
    (∏ j : Fin 9,
        ∏ sigma : {sigma : GenHashSupportTriple // sigma.1 i = j},
          f sigma.1) =
        ∏ x : Sigma fun j : Fin 9 ↦
          {sigma : GenHashSupportTriple // sigma.1 i = j},
          f x.2.1 := by
      exact (Fintype.prod_sigma
        (fun x : Sigma fun j : Fin 9 ↦
          {sigma : GenHashSupportTriple // sigma.1 i = j} ↦
            f x.2.1)).symm
    _ = ∏ sigma : GenHashSupportTriple, f sigma := by
      exact
        (Equiv.prod_comp
          (Equiv.sigmaFiberEquiv
            (fun sigma : GenHashSupportTriple ↦ sigma.1 i)) f)

private theorem genHashCompletion_row_multinomial_factorization
    (base : Fin 10 → ℕ) (m : ℕ) (i : Fin 3) (k : GenHashJointMultiplicityTable)
    (hkMarginal : ∀ j : Fin 9,
      (∑ sigma : {sigma : GenHashSupportTriple // sigma.1 i = j},
        k sigma.1) = genMarginalCount base m j) :
    (∏ j : Fin 9,
        Nat.multinomial Finset.univ
          (fun sigma : {sigma : GenHashSupportTriple // sigma.1 i = j} ↦
            k sigma.1)) =
      (∏ j : Fin 9, (genMarginalCount base m j).factorial) /
        ∏ sigma : GenHashSupportTriple, (k sigma).factorial := by
  classical
  have hrowDiv (j : Fin 9) :
      (∏ sigma : {sigma : GenHashSupportTriple // sigma.1 i = j},
        (k sigma.1).factorial) ∣
          (genMarginalCount base m j).factorial := by
    have h := Nat.prod_factorial_dvd_factorial_sum
      (Finset.univ : Finset
        {sigma : GenHashSupportTriple // sigma.1 i = j})
      (fun sigma ↦ k sigma.1)
    simpa [hkMarginal j] using h
  simp only [Nat.multinomial]
  simp_rw [hkMarginal]
  calc
    (∏ j : Fin 9,
        (genMarginalCount base m j).factorial /
          ∏ sigma : {sigma : GenHashSupportTriple // sigma.1 i = j},
            (k sigma.1).factorial) =
        (∏ j : Fin 9, (genMarginalCount base m j).factorial) /
          ∏ j : Fin 9,
            ∏ sigma : {sigma : GenHashSupportTriple // sigma.1 i = j},
              (k sigma.1).factorial := by
      exact genHashCompletion_prod_nat_div_eq_div_prod_of_dvd
        (Finset.univ : Finset (Fin 9))
        (fun j ↦ (genMarginalCount base m j).factorial)
        (fun j ↦
          ∏ sigma : {sigma : GenHashSupportTriple // sigma.1 i = j},
            (k sigma.1).factorial)
        (by
          intro j _
          exact hrowDiv j)
    _ = (∏ j : Fin 9, (genMarginalCount base m j).factorial) /
        ∏ sigma : GenHashSupportTriple, (k sigma).factorial := by
      exact congrArg
        (fun d : ℕ ↦
          (∏ j : Fin 9, (genMarginalCount base m j).factorial) / d)
        (genHashCompletion_prod_over_coordinate i
          (fun sigma : GenHashSupportTriple ↦ (k sigma).factorial))


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
    (((∏ j : Fin 9, (genMarginalCount base m j).factorial) /
        ∏ sigma : GenHashSupportTriple, (k sigma).factorial : ℕ) : ℝ) ≤
      (6 * (((genOuterLength base m + 1 : ℕ) : ℝ))) ^ 45 *
        (genHashTargetStarDegree bstar m : ℝ) := by
  have htargetMarg : ∀ j : Fin 9,
      (∑ sigma : {sigma : GenHashSupportTriple // sigma.1 i = j},
        genHashTargetJointTable bstar m sigma.1) =
        genMarginalCount base m j := by
    intro j
    rw [mme_stothers_general_outer_profile_arithmetic.2.2.2 bstar m i j]
    simp only [genMarginalCount, hsame j]
  have hstar :
      genHashTargetStarDegree bstar m =
        (∏ j : Fin 9, (genMarginalCount base m j).factorial) /
          ∏ sigma : GenHashSupportTriple,
            (genHashTargetJointTable bstar m sigma).factorial := by
    simp only [genHashTargetStarDegree]
    congr 1
    apply Finset.prod_congr rfl
    intro j _
    simp only [genMarginalCount, hsame j]
  have hrow :=
    mme_stothers_general_mode_row_multinomial_le
      base bstar m hm hbase hsame i k hkMarginal hcond
  have hcandidate :=
    genHashCompletion_row_multinomial_factorization base m i k (hkMarginal i)
  have htarget :=
    genHashCompletion_row_multinomial_factorization base m i
      (genHashTargetJointTable bstar m) htargetMarg
  rw [hstar, ← hcandidate, ← htarget]
  simpa only [Nat.cast_prod] using hrow
