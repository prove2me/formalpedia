-- Prove2me | solution 1 for mme_stothers_general_exact_target_subtype_nat_card
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-09-08T05:15:05.183858+00:00
-- url     : https://prove2.me/submissions/c3b6b3b1-0d14-4da4-af23-631ca43abaa7

import Definitions.Def_mme_stothers_general_outer_profile
import Theorems.Thm_mme_stothers_general_outer_profile_arithmetic
import Theorems.Thm_mme_stothers_general_exact_outer_address_regular
import Theorems.Thm_mme_fintype_prescribed_fiber_function_card

open MME BigOperators

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace MME.StothersFourth.GeneralProfileCount

private theorem orbit_support (r : Fin 10) (sigma : Fin 3 → Fin 9)
    (h : genSameOrbitExplicit sigma (classRep r)) :
    (∑ s, (sigma s).val) = 8 := by
  have hrep : (∑ s, (classRep r s).val) = 8 := by
    fin_cases r <;>
      norm_num [classRep, cwFourthBlockType, Fin.sum_univ_three]
  rcases h with h | h | h | h | h | h <;>
    rcases h with ⟨h0, h1, h2⟩ <;>
    simp only [Fin.sum_univ_three, h0, h1, h2] at * <;>
    omega

private theorem zero_outside_support
    (base : Fin 10 → ℕ) (m : ℕ) (sigma : Fin 3 → Fin 9)
    (hsigma : (∑ s, (sigma s).val) ≠ 8) :
    genJointMultiplicity base m sigma = 0 := by
  unfold genJointMultiplicity
  apply Finset.sum_eq_zero
  intro r _
  rw [if_neg]
  intro hOrbit
  exact hsigma (orbit_support r sigma hOrbit)

private theorem marginal_sum (base : Fin 10 → ℕ) (m : ℕ) :
    ∑ j : Fin 9, genMarginalCount base m j = genOuterLength base m := by
  simp only [genMarginalCount]
  rw [← Finset.sum_mul,
    mme_stothers_general_outer_profile_arithmetic.2.1 base]
  simp only [genOuterLength]
  ac_rfl

end MME.StothersFourth.GeneralProfileCount

open MME.StothersFourth
open MME.StothersFourth.GeneralProfileCount

theorem solution (base : Fin 10 → ℕ) (m : ℕ) :
    Nat.card
        {a : GenMarginalSupportedAddress base m //
          GenHasExactJointProfile a} =
      (genOuterLength base m).factorial /
        ∏ sigma : GenHashSupportTriple,
          (genHashTargetJointTable base m sigma).factorial := by
  classical
  let jointAt (a : GenExactOuterAddress base m)
      (j : Fin (genOuterLength base m)) : GenHashSupportTriple :=
    ⟨genAddressType a.1 j,
      (mme_stothers_general_exact_outer_address_regular base m a).1 j⟩
  let Assignment :=
    {g : Fin (genOuterLength base m) → GenHashSupportTriple //
      ∀ sigma, Fintype.card {j // g j = sigma} =
        genHashTargetJointTable base m sigma}
  have hzero : ∀ sigma : Fin 3 → Fin 9,
      (∑ s, (sigma s).val) ≠ 8 →
        genJointMultiplicity base m sigma = 0 := by
    intro sigma hsigma
    exact zero_outside_support base m sigma hsigma
  let eExact : GenExactOuterAddress base m ≃ Assignment := {
    toFun a := ⟨jointAt a, by
      intro sigma
      rw [Fintype.card_subtype]
      simpa only [jointAt, genHashTargetJointTable, genAddressType,
        Subtype.ext_iff] using a.2 sigma.1⟩
    invFun G := by
      let raw : GenOuterAddress base m := fun i j ↦ (G.1 j).1 i
      refine ⟨raw, ?_⟩
      intro sigma
      by_cases hsigma : (∑ s, (sigma s).val) = 8
      · let sigma' : GenHashSupportTriple := ⟨sigma, hsigma⟩
        have h := G.2 sigma'
        rw [Fintype.card_subtype] at h
        simpa only [raw, genAddressType, genHashTargetJointTable,
          sigma', Subtype.ext_iff] using h
      · rw [hzero sigma hsigma]
        apply Finset.card_eq_zero.mpr
        rw [Finset.filter_eq_empty_iff]
        intro j _ hj
        have hjEq : (G.1 j).1 = sigma := by
          simpa only [raw, genAddressType] using hj
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
    {a : GenMarginalSupportedAddress base m // GenHasExactJointProfile a}
  let eTarget : GenExactOuterAddress base m ≃ Target := {
    toFun a := by
      have hregular := mme_stothers_general_exact_outer_address_regular base m a
      let b : GenMarginalSupportedAddress base m :=
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
      (∑ sigma : GenHashSupportTriple,
        genHashTargetJointTable base m sigma) = genOuterLength base m := by
    rw [← Fintype.sum_fiberwise
      (fun sigma : GenHashSupportTriple ↦ sigma.1 0)
      (genHashTargetJointTable base m)]
    simp_rw [mme_stothers_general_outer_profile_arithmetic.2.2.2 base m 0]
    exact marginal_sum base m
  have hcount := mme_fintype_prescribed_fiber_function_card
    (α := Fin (genOuterLength base m))
    (ι := GenHashSupportTriple)
    (genHashTargetJointTable base m)
    (by simpa only [Fintype.card_fin] using hsum)
  calc
    Nat.card Target = Nat.card (GenExactOuterAddress base m) :=
      (Nat.card_congr eTarget).symm
    _ = Nat.card Assignment := Nat.card_congr eExact
    _ = Fintype.card Assignment := Nat.card_eq_fintype_card
    _ = (genOuterLength base m).factorial /
        ∏ sigma : GenHashSupportTriple,
          (genHashTargetJointTable base m sigma).factorial := by
      simpa only [Assignment, Fintype.card_fin] using hcount
