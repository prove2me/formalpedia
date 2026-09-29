-- Prove2me | solution 1 for mme_stothers_general_hash_conditional_entropy_of_stationary
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-09-09T04:59:06.329044+00:00
-- url     : https://prove2.me/submissions/ebb06c4f-a988-4243-8284-74d5b3846f92

import Definitions.Def_mme_stothers_general_outer_profile
import Definitions.Def_mme_modern_entropy_data
import Theorems.Thm_mme_stothers_general_mode_conditional_entropy_maximal
import Theorems.Thm_mme_stothers_general_joint_entropy_maximal

open MME BigOperators

set_option autoImplicit false
set_option warningAsError true

namespace MME.StothersFourth.GenScale

/-- Each row of the nine-grade marginal matrix sums to three times the class
multiplicity, so the total marginal mass of a profile is `3D`. -/
private theorem row_sum (r : Fin 10) :
    (∑ j : Fin 9, genClassMarginalMultiplicity r j) = 3 * classMultiplicity r := by
  fin_cases r <;> decide

private theorem marginal_total (b : Fin 10 → ℕ) :
    (∑ j : Fin 9, genMarginalBaseCount b j) = 3 * genProfileScale b := by
  simp only [genMarginalBaseCount, genProfileScale]
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro r _
  rw [← Finset.sum_mul, row_sum r]
  ring

theorem scale_eq_of_same_marginals (base bstar : Fin 10 → ℕ)
    (hsame : ∀ j, genMarginalBaseCount bstar j = genMarginalBaseCount base j) :
    genProfileScale bstar = genProfileScale base := by
  have h : (∑ j : Fin 9, genMarginalBaseCount bstar j) =
      ∑ j : Fin 9, genMarginalBaseCount base j :=
    Finset.sum_congr rfl (fun j _ => hsame j)
  rw [marginal_total, marginal_total] at h
  omega

private theorem joint_scale (b : Fin 10 → ℕ) (m : ℕ) (sigma : Fin 3 → Fin 9) :
    genJointMultiplicity b m sigma = m * genJointMultiplicity b 1 sigma := by
  simp only [genJointMultiplicity, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro r _
  by_cases h : genSameOrbitExplicit sigma (classRep r)
  · simp [h, genProfileCount, Nat.mul_comm]
  · simp [h]

/-- At every positive scale the target histogram of `bstar`, normalised by the
address length of `base`, is the scale-one target histogram of `bstar`. -/
theorem target_eq_scale_one (base bstar : Fin 10 → ℕ) (m : ℕ) (hm : 0 < m)
    (hsame : ∀ j, genMarginalBaseCount bstar j = genMarginalBaseCount base j)
    (sigma : GenHashSupportTriple) :
    ((genHashTargetJointTable bstar m sigma : ℝ) / (genOuterLength base m : ℝ)) =
      (genJointMultiplicity bstar 1 sigma.1 : ℝ) / (genOuterLength bstar 1 : ℝ) := by
  have hscale := scale_eq_of_same_marginals base bstar hsame
  have hnum : genHashTargetJointTable bstar m sigma = m * genJointMultiplicity bstar 1 sigma.1 :=
    joint_scale bstar m sigma.1
  have hden : genOuterLength base m = m * genOuterLength bstar 1 := by
    simp only [genOuterLength, hscale]
    ring
  have hmR : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  rw [hnum, hden]
  push_cast
  field_simp

end MME.StothersFourth.GenScale

open MME.StothersFourth.GenScale

theorem mme_stothers_general_hash_joint_entropy_maximal_at_scale
    (base bstar : Fin 10 → ℕ) (m : ℕ) (hm : 0 < m)
    (hbstar : ∀ r, 0 < bstar r)
    (hsame : ∀ j, MME.StothersFourth.genMarginalBaseCount bstar j =
      MME.StothersFourth.genMarginalBaseCount base j)
    (hInN : MME.StothersFourth.InN (MME.StothersFourth.genProfileB bstar)) :
    ∀ rho : MME.StothersFourth.GenHashSupportTriple → ℝ,
      (∀ sigma, 0 ≤ rho sigma) →
      (∑ sigma, rho sigma) = 1 →
      (∀ l : Fin 3, ∀ j : Fin 9,
        mme_modern_marginal
            (fun sigma : MME.StothersFourth.GenHashSupportTriple ↦ sigma.1 l) rho j =
          mme_modern_marginal
            (fun sigma : MME.StothersFourth.GenHashSupportTriple ↦ sigma.1 l)
            (fun sigma ↦
              (MME.StothersFourth.genHashTargetJointTable bstar m sigma : ℝ) /
                (MME.StothersFourth.genOuterLength base m : ℝ)) j) →
      mme_modern_entropyBits rho ≤
        mme_modern_entropyBits
          (fun sigma ↦
            (MME.StothersFourth.genHashTargetJointTable bstar m sigma : ℝ) /
              (MME.StothersFourth.genOuterLength base m : ℝ)) := by
  have hEq :
      (fun sigma : MME.StothersFourth.GenHashSupportTriple ↦
          (MME.StothersFourth.genHashTargetJointTable bstar m sigma : ℝ) /
            (MME.StothersFourth.genOuterLength base m : ℝ)) =
        fun sigma : MME.StothersFourth.GenHashSupportTriple ↦
          (MME.StothersFourth.genJointMultiplicity bstar 1 sigma.1 : ℝ) /
            (MME.StothersFourth.genOuterLength bstar 1 : ℝ) :=
    funext (target_eq_scale_one base bstar m hm hsame)
  rw [hEq]
  exact mme_stothers_general_joint_entropy_maximal bstar hbstar hInN

theorem solution
    (base bstar : Fin 10 → ℕ)
    (hbase : ∀ r, 0 < base r) (hbstar : ∀ r, 0 < bstar r)
    (hsame : ∀ j, MME.StothersFourth.genMarginalBaseCount bstar j =
      MME.StothersFourth.genMarginalBaseCount base j)
    (hInN : MME.StothersFourth.InN (MME.StothersFourth.genProfileB bstar)) :
    ∀ (m : ℕ) (k : MME.StothersFourth.GenHashJointMultiplicityTable),
      (∀ l : Fin 3, ∀ j : Fin 9,
        (∑ sigma : {sigma : MME.StothersFourth.GenHashSupportTriple // sigma.1 l = j},
          k sigma.1) = MME.StothersFourth.genMarginalCount base m j) →
      ∀ i : Fin 3,
      (∑ j : Fin 9, (MME.StothersFourth.genMarginalCount base m j : ℝ) *
        mme_modern_entropyBits
          (fun sigma : {sigma : MME.StothersFourth.GenHashSupportTriple // sigma.1 i = j} ↦
            (k sigma.1 : ℝ) / (MME.StothersFourth.genMarginalCount base m j : ℝ))) ≤
      ∑ j : Fin 9, (MME.StothersFourth.genMarginalCount base m j : ℝ) *
        mme_modern_entropyBits
          (fun sigma : {sigma : MME.StothersFourth.GenHashSupportTriple // sigma.1 i = j} ↦
            (MME.StothersFourth.genHashTargetJointTable bstar m sigma.1 : ℝ) /
              (MME.StothersFourth.genMarginalCount base m j : ℝ)) := by
  intro m k hk i
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simp [MME.StothersFourth.genMarginalCount]
  · exact mme_stothers_general_mode_conditional_entropy_maximal base bstar m hm hbase
      hsame i k hk
      (mme_stothers_general_hash_joint_entropy_maximal_at_scale base bstar m hm hbstar
        hsame hInN)
