-- Prove2me | solution 1 for MME.StothersFourth.mme_stothers_fixed_exact_target_subtype_nat_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T21:18:55.709893+00:00
-- url     : https://prove2.me/submissions/0c124844-9ad7-40d9-b371-c9d799847dbb

import Definitions.Def_mme_stothers_fixed_outer_profile
import Definitions.Def_mme_stothers_fixed_joint_tables
import Theorems.Thm_mme_stothers_fixed_outer_profile_arithmetic
import Theorems.Thm_mme_stothers_fixed_exact_outer_address_regular
import Theorems.Thm_MME_StothersFourth_mme_stothers_fixed_target_joint_table_marginal
import Theorems.Thm_mme_fintype_prescribed_fiber_function_card

open MME BigOperators

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace MME.StothersFourth

private theorem fixedHashExactCount_orbit_support :
    ∀ (q : Fin 10) (sigma : Fin 3 → Fin 9),
      fixedSameOrbitExplicit sigma (classRep q) →
        (∑ s, (sigma s).val) = 8 := by
  intro q sigma h
  have hrep : (∑ s, (classRep q s).val) = 8 := by
    fin_cases q <;>
      norm_num [classRep, cwFourthBlockType, Fin.sum_univ_three]
  rcases h with h | h | h | h | h | h <;>
    rcases h with ⟨h0, h1, h2⟩ <;>
    simp only [Fin.sum_univ_three, h0, h1, h2] at * <;>
    omega

private theorem fixedHashExactCount_zero_outside_support
    (m : ℕ) (sigma : Fin 3 → Fin 9)
    (hsigma : (∑ s, (sigma s).val) ≠ 8) :
    fixedJointMultiplicity m sigma = 0 := by
  unfold fixedJointMultiplicity
  apply Finset.sum_eq_zero
  intro q _
  rw [if_neg]
  intro hOrbit
  exact hsigma (fixedHashExactCount_orbit_support q sigma hOrbit)

private theorem fixedHashExactCount_marginal_sum (m : ℕ) :
    ∑ j : Fin 9, fixedMarginalCount m j = fixedOuterLength m := by
  simp only [fixedMarginalCount]
  rw [← Finset.mul_sum,
    mme_stothers_fixed_outer_profile_arithmetic.2.2.2.2.1]
  simp only [fixedOuterLength]
  ac_rfl

end MME.StothersFourth

open MME.StothersFourth

theorem solution (m : ℕ) :
    Nat.card
        {a : FixedMarginalSupportedAddress m //
          FixedHasExactJointProfile a} =
      (fixedOuterLength m).factorial /
        ∏ sigma : FixedHashSupportTriple,
          (fixedHashTargetJointTable m sigma).factorial := by
  classical
  let jointAt (a : FixedExactOuterAddress m)
      (j : Fin (fixedOuterLength m)) : FixedHashSupportTriple :=
    ⟨fixedAddressType a.1 j,
      (mme_stothers_fixed_exact_outer_address_regular m a).1 j⟩
  let Assignment :=
    {g : Fin (fixedOuterLength m) → FixedHashSupportTriple //
      ∀ sigma, Fintype.card {j // g j = sigma} =
        fixedHashTargetJointTable m sigma}
  have hzero : ∀ sigma : Fin 3 → Fin 9,
      (∑ s, (sigma s).val) ≠ 8 →
        fixedJointMultiplicity m sigma = 0 := by
    intro sigma hsigma
    exact fixedHashExactCount_zero_outside_support m sigma hsigma
  let eExact : FixedExactOuterAddress m ≃ Assignment := {
    toFun a := ⟨jointAt a, by
      intro sigma
      rw [Fintype.card_subtype]
      simpa only [jointAt, fixedHashTargetJointTable, fixedAddressType,
        Subtype.ext_iff] using a.2 sigma.1⟩
    invFun G := by
      let raw : FixedOuterAddress m := fun i j ↦ (G.1 j).1 i
      refine ⟨raw, ?_⟩
      intro sigma
      by_cases hsigma : (∑ s, (sigma s).val) = 8
      · let sigma' : FixedHashSupportTriple := ⟨sigma, hsigma⟩
        have h := G.2 sigma'
        rw [Fintype.card_subtype] at h
        simpa only [raw, fixedAddressType, fixedHashTargetJointTable,
          sigma', Subtype.ext_iff] using h
      · rw [hzero sigma hsigma]
        apply Finset.card_eq_zero.mpr
        rw [Finset.filter_eq_empty_iff]
        intro j _ hj
        have hjEq : (G.1 j).1 = sigma := by
          simpa only [raw, fixedAddressType] using hj
        exact hsigma (hjEq ▸ (G.1 j).2)
    left_inv a := by
      apply Subtype.ext
      funext i j
      rfl
    right_inv G := by
      apply Subtype.ext
      funext j
      apply Subtype.ext
      rfl
  }
  let Target :=
    {a : FixedMarginalSupportedAddress m //
      FixedHasExactJointProfile a}
  let eTarget : FixedExactOuterAddress m ≃ Target := {
    toFun a := by
      have hregular := mme_stothers_fixed_exact_outer_address_regular m a
      let b : FixedMarginalSupportedAddress m :=
        ⟨a.1, hregular.1, hregular.2⟩
      exact ⟨b, a.2⟩
    invFun a := ⟨a.1.1, a.2⟩
    left_inv a := by
      apply Subtype.ext
      rfl
    right_inv a := by
      apply Subtype.ext
      apply Subtype.ext
      rfl
  }
  have hsum :
      (∑ sigma : FixedHashSupportTriple,
        fixedHashTargetJointTable m sigma) = fixedOuterLength m := by
    rw [← Fintype.sum_fiberwise
      (fun sigma : FixedHashSupportTriple ↦ sigma.1 0)
      (fixedHashTargetJointTable m)]
    simp_rw [mme_stothers_fixed_target_joint_table_marginal m 0]
    exact fixedHashExactCount_marginal_sum m
  have hcount := mme_fintype_prescribed_fiber_function_card
    (α := Fin (fixedOuterLength m))
    (ι := FixedHashSupportTriple)
    (fixedHashTargetJointTable m)
    (by simpa only [Fintype.card_fin] using hsum)
  calc
    Nat.card Target = Nat.card (FixedExactOuterAddress m) :=
      (Nat.card_congr eTarget).symm
    _ = Nat.card Assignment := Nat.card_congr eExact
    _ = Fintype.card Assignment := Nat.card_eq_fintype_card
    _ = (fixedOuterLength m).factorial /
        ∏ sigma : FixedHashSupportTriple,
          (fixedHashTargetJointTable m sigma).factorial := by
      simpa only [Assignment, Fintype.card_fin] using hcount
