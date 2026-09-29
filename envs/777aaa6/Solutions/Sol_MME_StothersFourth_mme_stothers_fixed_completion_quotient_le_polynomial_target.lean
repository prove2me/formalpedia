-- Prove2me | solution 1 for MME.StothersFourth.mme_stothers_fixed_completion_quotient_le_polynomial_target
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T21:06:17.330927+00:00
-- url     : https://prove2.me/submissions/b243d3d6-a5fc-4b31-8ec9-3e0c5fc83356

import Definitions.Def_mme_stothers_fixed_outer_profile
import Definitions.Def_mme_stothers_fixed_joint_tables
import Theorems.Thm_MME_StothersFourth_mme_stothers_fixed_target_joint_table_marginal
import Theorems.Thm_MME_StothersFourth_mme_stothers_fixed_mode_row_multinomial_le

open MME BigOperators

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000

namespace MME.StothersFourth

private theorem fixedHashCompletion_prod_nat_div_eq_div_prod_of_dvd
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

private theorem fixedHashCompletion_prod_over_coordinate
    (i : Fin 3) (f : FixedHashSupportTriple → ℕ) :
    (∏ j : Fin 9,
      ∏ sigma : {sigma : FixedHashSupportTriple // sigma.1 i = j},
        f sigma.1) = ∏ sigma : FixedHashSupportTriple, f sigma := by
  classical
  calc
    (∏ j : Fin 9,
        ∏ sigma : {sigma : FixedHashSupportTriple // sigma.1 i = j},
          f sigma.1) =
        ∏ x : Sigma fun j : Fin 9 ↦
          {sigma : FixedHashSupportTriple // sigma.1 i = j},
          f x.2.1 := by
      exact (Fintype.prod_sigma
        (fun x : Sigma fun j : Fin 9 ↦
          {sigma : FixedHashSupportTriple // sigma.1 i = j} ↦
            f x.2.1)).symm
    _ = ∏ sigma : FixedHashSupportTriple, f sigma := by
      simpa only using
        (Equiv.prod_comp
          (Equiv.sigmaFiberEquiv
            (fun sigma : FixedHashSupportTriple ↦ sigma.1 i)) f)

private theorem fixedHashCompletion_row_multinomial_factorization
    (m : ℕ) (i : Fin 3) (k : FixedHashJointMultiplicityTable)
    (hkMarginal : ∀ j : Fin 9,
      (∑ sigma : {sigma : FixedHashSupportTriple // sigma.1 i = j},
        k sigma.1) = fixedMarginalCount m j) :
    (∏ j : Fin 9,
        Nat.multinomial Finset.univ
          (fun sigma : {sigma : FixedHashSupportTriple // sigma.1 i = j} ↦
            k sigma.1)) =
      (∏ j : Fin 9, (fixedMarginalCount m j).factorial) /
        ∏ sigma : FixedHashSupportTriple, (k sigma).factorial := by
  classical
  have hrowDiv (j : Fin 9) :
      (∏ sigma : {sigma : FixedHashSupportTriple // sigma.1 i = j},
        (k sigma.1).factorial) ∣
          (fixedMarginalCount m j).factorial := by
    have h := Nat.prod_factorial_dvd_factorial_sum
      (Finset.univ : Finset
        {sigma : FixedHashSupportTriple // sigma.1 i = j})
      (fun sigma ↦ k sigma.1)
    simpa [hkMarginal j] using h
  simp only [Nat.multinomial]
  simp_rw [hkMarginal]
  calc
    (∏ j : Fin 9,
        (fixedMarginalCount m j).factorial /
          ∏ sigma : {sigma : FixedHashSupportTriple // sigma.1 i = j},
            (k sigma.1).factorial) =
        (∏ j : Fin 9, (fixedMarginalCount m j).factorial) /
          ∏ j : Fin 9,
            ∏ sigma : {sigma : FixedHashSupportTriple // sigma.1 i = j},
              (k sigma.1).factorial := by
      exact fixedHashCompletion_prod_nat_div_eq_div_prod_of_dvd
        (Finset.univ : Finset (Fin 9))
        (fun j ↦ (fixedMarginalCount m j).factorial)
        (fun j ↦
          ∏ sigma : {sigma : FixedHashSupportTriple // sigma.1 i = j},
            (k sigma.1).factorial)
        (by
          intro j _
          exact hrowDiv j)
    _ = (∏ j : Fin 9, (fixedMarginalCount m j).factorial) /
        ∏ sigma : FixedHashSupportTriple, (k sigma).factorial := by
      exact congrArg
        (fun d : ℕ ↦
          (∏ j : Fin 9, (fixedMarginalCount m j).factorial) / d)
        (fixedHashCompletion_prod_over_coordinate i
          (fun sigma : FixedHashSupportTriple ↦ (k sigma).factorial))

end MME.StothersFourth

theorem solution
    (m : ℕ) (hm : 0 < m) (i : Fin 3)
    (k : MME.StothersFourth.FixedHashJointMultiplicityTable)
    (hkMarginal : ∀ l : Fin 3, ∀ j : Fin 9,
      (∑ sigma : {sigma : MME.StothersFourth.FixedHashSupportTriple //
          sigma.1 l = j}, k sigma.1) =
        MME.StothersFourth.fixedMarginalCount m j) :
    (((∏ j : Fin 9,
          (MME.StothersFourth.fixedMarginalCount m j).factorial) /
        ∏ sigma : MME.StothersFourth.FixedHashSupportTriple,
          (k sigma).factorial : ℕ) : ℝ) ≤
      (6 * (((MME.StothersFourth.fixedOuterLength m + 1 : ℕ) : ℝ))) ^ 45 *
        (MME.StothersFourth.fixedHashTargetStarDegree m : ℝ) := by
  have hrow :=
    MME.StothersFourth.mme_stothers_fixed_mode_row_multinomial_le
      m hm i k hkMarginal
  have hcandidate :=
    MME.StothersFourth.fixedHashCompletion_row_multinomial_factorization
      m i k (hkMarginal i)
  have htarget :=
    MME.StothersFourth.fixedHashCompletion_row_multinomial_factorization
      m i (MME.StothersFourth.fixedHashTargetJointTable m)
        (MME.StothersFourth.mme_stothers_fixed_target_joint_table_marginal
          m i)
  change
    (((∏ j : Fin 9,
          (MME.StothersFourth.fixedMarginalCount m j).factorial) /
        ∏ sigma : MME.StothersFourth.FixedHashSupportTriple,
          (k sigma).factorial : ℕ) : ℝ) ≤
      (6 * (((MME.StothersFourth.fixedOuterLength m + 1 : ℕ) : ℝ))) ^ 45 *
        (((∏ j : Fin 9,
            (MME.StothersFourth.fixedMarginalCount m j).factorial) /
          ∏ sigma : MME.StothersFourth.FixedHashSupportTriple,
            (MME.StothersFourth.fixedHashTargetJointTable m sigma).factorial :
              ℕ) : ℝ)
  rw [← hcandidate, ← htarget]
  simpa only [Nat.cast_prod] using hrow
