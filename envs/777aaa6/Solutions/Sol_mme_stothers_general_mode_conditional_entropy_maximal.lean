-- Prove2me | solution 1 for mme_stothers_general_mode_conditional_entropy_maximal
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-09-08T05:44:41.539646+00:00
-- url     : https://prove2.me/submissions/67eb8807-4f15-42ad-83d9-35f532de38e2

import Definitions.Def_mme_stothers_general_outer_profile
import Definitions.Def_mme_modern_entropy_data
import Theorems.Thm_mme_stothers_general_outer_profile_arithmetic
import Mathlib.Algebra.BigOperators.Field

open MME BigOperators

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000

namespace MME.StothersFourth

private theorem genHashConditional_entropy_chain_rule
    {D J : Type*} [Fintype D] [Fintype J] [DecidableEq J]
    (coord : D → J) (p : D → ℝ) (q : J → ℝ)
    (hq : ∀ j, q j = ∑ x : {x : D // coord x = j}, p x.1)
    (hqpos : ∀ j, 0 < q j) :
    mme_modern_entropyBits p =
      mme_modern_entropyBits q +
        ∑ j, q j * mme_modern_entropyBits
          (fun x : {x : D // coord x = j} ↦ p x.1 / q j) := by
  classical
  have hrow (j : J) :
      (∑ x : {x : D // coord x = j}, Real.negMulLog (p x.1)) =
        Real.negMulLog (q j) +
          q j * ∑ x : {x : D // coord x = j},
            Real.negMulLog (p x.1 / q j) := by
    have hqne : q j ≠ 0 := ne_of_gt (hqpos j)
    calc
      (∑ x : {x : D // coord x = j}, Real.negMulLog (p x.1)) =
          ∑ x : {x : D // coord x = j},
            Real.negMulLog (q j * (p x.1 / q j)) := by
        apply Finset.sum_congr rfl
        intro x _
        congr 1
        field_simp
      _ = ∑ x : {x : D // coord x = j},
          ((p x.1 / q j) * Real.negMulLog (q j) +
            q j * Real.negMulLog (p x.1 / q j)) := by
        apply Finset.sum_congr rfl
        intro x _
        exact Real.negMulLog_mul _ _
      _ = Real.negMulLog (q j) +
          q j * ∑ x : {x : D // coord x = j},
            Real.negMulLog (p x.1 / q j) := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
        have hsum :
            (∑ x : {x : D // coord x = j}, p x.1 / q j) = 1 := by
          rw [← Finset.sum_div, ← hq j]
          exact div_self hqne
        rw [hsum]
        ring
  unfold mme_modern_entropyBits
  rw [← Fintype.sum_fiberwise coord (fun x ↦ Real.negMulLog (p x))]
  simp_rw [hrow]
  rw [Finset.sum_add_distrib]
  simp only [div_eq_mul_inv]
  have hfactor :
      (∑ j, q j *
        ((∑ x : {x : D // coord x = j},
          Real.negMulLog (p x.1 * (q j)⁻¹)) * (Real.log 2)⁻¹)) =
        (∑ j, q j *
          ∑ x : {x : D // coord x = j},
            Real.negMulLog (p x.1 * (q j)⁻¹)) * (Real.log 2)⁻¹ := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hfactor]
  ring


private theorem genCondMarginalCountSum (base : Fin 10 → ℕ) (m : ℕ) :
    ∑ j : Fin 9, genMarginalCount base m j = genOuterLength base m := by
  simp only [genMarginalCount]
  rw [← Finset.sum_mul,
    mme_stothers_general_outer_profile_arithmetic.2.1 base]
  simp only [genOuterLength]
  ac_rfl

private theorem genCondScalePos (base : Fin 10 → ℕ)
    (hbase : ∀ r, 0 < base r) : 0 < genProfileScale base := by
  refine Finset.sum_pos' (fun i _ ↦ Nat.zero_le _)
    ⟨0, Finset.mem_univ 0, ?_⟩
  have h0 := hbase 0
  simpa [classMultiplicity] using h0

private theorem genCondOuterLengthPos (base : Fin 10 → ℕ) (m : ℕ)
    (hm : 0 < m) (hbase : ∀ r, 0 < base r) : 0 < genOuterLength base m := by
  simp only [genOuterLength]
  exact Nat.mul_pos (by norm_num)
    (Nat.mul_pos (genCondScalePos base hbase) hm)

private theorem genCondMarginalBasePos (base : Fin 10 → ℕ)
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

private theorem genCondMarginalCountPos (base : Fin 10 → ℕ) (m : ℕ)
    (hm : 0 < m) (hbase : ∀ r, 0 < base r) (j : Fin 9) :
    0 < genMarginalCount base m j :=
  Nat.mul_pos (genCondMarginalBasePos base hbase j) hm

private theorem genCondJointTableSum (base : Fin 10 → ℕ) (m : ℕ)
    (k : GenHashJointMultiplicityTable)
    (hkMarginal : ∀ l : Fin 3, ∀ j : Fin 9,
      (∑ sigma : {sigma : GenHashSupportTriple // sigma.1 l = j},
        k sigma.1) = genMarginalCount base m j) :
    ∑ sigma, k sigma = genOuterLength base m := by
  rw [← Fintype.sum_fiberwise
    (fun sigma : GenHashSupportTriple ↦ sigma.1 0) k]
  simp_rw [hkMarginal 0]
  exact genCondMarginalCountSum base m

private theorem genCondTargetMarginal (base bstar : Fin 10 → ℕ) (m : ℕ)
    (hsame : ∀ j, genMarginalBaseCount bstar j = genMarginalBaseCount base j)
    (l : Fin 3) (j : Fin 9) :
    (∑ sigma : {sigma : GenHashSupportTriple // sigma.1 l = j},
      genHashTargetJointTable bstar m sigma.1) = genMarginalCount base m j := by
  rw [mme_stothers_general_outer_profile_arithmetic.2.2.2 bstar m l j]
  simp only [genMarginalCount, hsame j]

private theorem genCondTargetTableSum (base bstar : Fin 10 → ℕ) (m : ℕ)
    (hsame : ∀ j, genMarginalBaseCount bstar j = genMarginalBaseCount base j) :
    ∑ sigma : GenHashSupportTriple,
        genHashTargetJointTable bstar m sigma = genOuterLength base m := by
  rw [← Fintype.sum_fiberwise
    (fun sigma : GenHashSupportTriple ↦ sigma.1 0)
    (genHashTargetJointTable bstar m)]
  simp_rw [genCondTargetMarginal base bstar m hsame 0]
  exact genCondMarginalCountSum base m

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
    (hjoint : ∀ rho : GenHashSupportTriple → ℝ,
      (∀ sigma, 0 ≤ rho sigma) →
      (∑ sigma, rho sigma) = 1 →
      (∀ l : Fin 3, ∀ j : Fin 9,
        mme_modern_marginal (fun sigma : GenHashSupportTriple ↦ sigma.1 l)
            rho j =
          mme_modern_marginal (fun sigma : GenHashSupportTriple ↦ sigma.1 l)
            (fun sigma ↦ (genHashTargetJointTable bstar m sigma : ℝ) /
              (genOuterLength base m : ℝ)) j) →
      mme_modern_entropyBits rho ≤
        mme_modern_entropyBits
          (fun sigma ↦ (genHashTargetJointTable bstar m sigma : ℝ) /
            (genOuterLength base m : ℝ))) :
    (∑ j : Fin 9, (genMarginalCount base m j : ℝ) *
      mme_modern_entropyBits
        (fun sigma : {sigma : GenHashSupportTriple // sigma.1 i = j} ↦
          (k sigma.1 : ℝ) / (genMarginalCount base m j : ℝ))) ≤
      ∑ j : Fin 9, (genMarginalCount base m j : ℝ) *
        mme_modern_entropyBits
          (fun sigma : {sigma : GenHashSupportTriple // sigma.1 i = j} ↦
            (genHashTargetJointTable bstar m sigma.1 : ℝ) /
              (genMarginalCount base m j : ℝ)) := by
  classical
  let N : ℕ := genOuterLength base m
  let rho : GenHashSupportTriple → ℝ := fun sigma ↦ (k sigma : ℝ) / N
  let target : GenHashSupportTriple → ℝ := fun sigma ↦
    (genHashTargetJointTable bstar m sigma : ℝ) / N
  let q : Fin 9 → ℝ := fun j ↦ (genMarginalCount base m j : ℝ) / N
  have hNposNat : 0 < N := genCondOuterLengthPos base m hm hbase
  have hNne : (N : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hNposNat)
  have hqpos (j : Fin 9) : 0 < q j := by
    exact div_pos
      (by exact_mod_cast genCondMarginalCountPos base m hm hbase j)
      (by exact_mod_cast hNposNat)
  have hrhoSum : ∑ sigma, rho sigma = 1 := by
    dsimp only [rho]
    rw [← Finset.sum_div, ← Nat.cast_sum,
      genCondJointTableSum base m k hkMarginal]
    exact div_self hNne
  have htargetSum : ∑ sigma, target sigma = 1 := by
    dsimp only [target]
    rw [← Finset.sum_div, ← Nat.cast_sum,
      genCondTargetTableSum base bstar m hsame]
    exact div_self hNne
  have hrhoMarginal (l : Fin 3) (j : Fin 9) :
      q j = ∑ sigma : {sigma : GenHashSupportTriple // sigma.1 l = j},
        rho sigma.1 := by
    dsimp only [q, rho]
    rw [← Finset.sum_div, ← Nat.cast_sum, hkMarginal l j]
  have htargetMarginal (l : Fin 3) (j : Fin 9) :
      q j = ∑ sigma : {sigma : GenHashSupportTriple // sigma.1 l = j},
        target sigma.1 := by
    dsimp only [q, target]
    rw [← Finset.sum_div, ← Nat.cast_sum,
      genCondTargetMarginal base bstar m hsame l j]
  have hmax : mme_modern_entropyBits rho ≤
      mme_modern_entropyBits target := by
    apply hjoint rho
    · intro sigma
      positivity
    · exact hrhoSum
    · intro l j
      unfold mme_modern_marginal
      rw [← hrhoMarginal l j]
      exact htargetMarginal l j
  have hrhoChain := genHashConditional_entropy_chain_rule
    (fun sigma : GenHashSupportTriple ↦ sigma.1 i) rho q
    (hrhoMarginal i) hqpos
  have htargetChain := genHashConditional_entropy_chain_rule
    (fun sigma : GenHashSupportTriple ↦ sigma.1 i) target q
    (htargetMarginal i) hqpos
  have hconditional :
      (∑ j, q j * mme_modern_entropyBits
        (fun sigma : {sigma : GenHashSupportTriple // sigma.1 i = j} ↦
          rho sigma.1 / q j)) ≤
      ∑ j, q j * mme_modern_entropyBits
        (fun sigma : {sigma : GenHashSupportTriple // sigma.1 i = j} ↦
          target sigma.1 / q j) := by
    linarith
  have hrhoConditional (j : Fin 9) :
      (fun sigma : {sigma : GenHashSupportTriple // sigma.1 i = j} ↦
          rho sigma.1 / q j) =
        fun sigma ↦ (k sigma.1 : ℝ) /
          (genMarginalCount base m j : ℝ) := by
    funext sigma
    dsimp only [rho, q]
    have hmargne : (genMarginalCount base m j : ℝ) ≠ 0 := by
      exact_mod_cast
        (Nat.ne_of_gt (genCondMarginalCountPos base m hm hbase j))
    field_simp
  have htargetConditional (j : Fin 9) :
      (fun sigma : {sigma : GenHashSupportTriple // sigma.1 i = j} ↦
          target sigma.1 / q j) =
        fun sigma ↦ (genHashTargetJointTable bstar m sigma.1 : ℝ) /
          (genMarginalCount base m j : ℝ) := by
    funext sigma
    dsimp only [target, q]
    have hmargne : (genMarginalCount base m j : ℝ) ≠ 0 := by
      exact_mod_cast
        (Nat.ne_of_gt (genCondMarginalCountPos base m hm hbase j))
    field_simp
  simp_rw [hrhoConditional, htargetConditional] at hconditional
  have hNnonneg : (0 : ℝ) ≤ N := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hconditional hNnonneg
  dsimp only [q] at hscaled
  rw [Finset.mul_sum, Finset.mul_sum] at hscaled
  have hcancel (j : Fin 9) (x : ℝ) :
      (N : ℝ) * ((genMarginalCount base m j : ℝ) / (N : ℝ) * x) =
        (genMarginalCount base m j : ℝ) * x := by
    field_simp
  simpa only [hcancel] using hscaled

