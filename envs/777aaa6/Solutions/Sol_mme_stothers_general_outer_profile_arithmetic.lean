-- Prove2me | solution 1 for mme_stothers_general_outer_profile_arithmetic
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-09-08T05:08:53.028296+00:00
-- url     : https://prove2.me/submissions/06ff4700-97cb-4521-b197-06322632cbf2

import Definitions.Def_mme_stothers_general_outer_profile
import Definitions.Def_mme_stothers_fixed_outer_profile
import Theorems.Thm_mme_stothers_fixed_outer_profile_arithmetic

open MME BigOperators
open MME.StothersFourth

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000

namespace MME.StothersFourth.GeneralProfileArithmetic

private theorem sameOrbit_bridge (sigma rho : Fin 3 → Fin 9) :
    genSameOrbitExplicit sigma rho ↔ fixedSameOrbitExplicit sigma rho :=
  Iff.rfl

private theorem classOrbit_bridge (r : Fin 10) :
    genClassOrbit r = fixedClassOrbit r := by
  ext sigma
  simp only [genClassOrbit, fixedClassOrbit, Finset.mem_filter,
    Finset.mem_univ, true_and]
  exact sameOrbit_bridge sigma (classRep r)

private theorem marginalMultiplicity_bridge :
    genClassMarginalMultiplicity = fixedClassMarginalMultiplicity := rfl

theorem orbit_coordinate_count (r : Fin 10) (s : Fin 3) (j : Fin 9) :
    ((genClassOrbit r).filter (fun sigma ↦ sigma s = j)).card =
      genClassMarginalMultiplicity r j := by
  rw [classOrbit_bridge, marginalMultiplicity_bridge]
  exact mme_stothers_fixed_outer_profile_arithmetic.2.2.1 r s j

private theorem marginalMultiplicity_row_sum (r : Fin 10) :
    ∑ j : Fin 9, genClassMarginalMultiplicity r j = 3 * classMultiplicity r := by
  fin_cases r <;>
    simp [genClassMarginalMultiplicity, classMultiplicity, Fin.sum_univ_succ]

theorem marginal_base_sum (base : Fin 10 → ℕ) :
    ∑ j : Fin 9, genMarginalBaseCount base j = 3 * genProfileScale base := by
  simp only [genMarginalBaseCount, genProfileScale]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [← Finset.sum_mul, marginalMultiplicity_row_sum]
  ring

theorem marginal_base_eq_Q (base : Fin 10 → ℕ) (j : Fin 9) :
    (genMarginalBaseCount base j : ℝ) = Q (fun i ↦ (base i : ℝ)) j := by
  simp only [genMarginalBaseCount]
  push_cast
  fin_cases j <;>
    simp [genClassMarginalMultiplicity, Q, Fin.sum_univ_succ] <;> ring

/-! ### The 45-cell joint histogram has the prescribed nine-grade marginals -/

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

private theorem sum_ite_const_eq_card
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    (p : alpha → Prop) [DecidablePred p] (c : ℕ) :
    (∑ x : alpha, if p x then c else 0) =
      Fintype.card {x : alpha // p x} * c := by
  rw [Fintype.card_subtype]
  calc
    (∑ x : alpha, if p x then c else 0) =
        ∑ _x ∈ (Finset.univ.filter p), c := by
      rw [Finset.sum_filter]
    _ = (Finset.univ.filter p).card * c := by simp

private theorem class_card (l : Fin 3) (j : Fin 9) (r : Fin 10) :
    Fintype.card
        {sigma : {sigma : GenHashSupportTriple // sigma.1 l = j} //
          genSameOrbitExplicit sigma.1.1 (classRep r)} =
      genClassMarginalMultiplicity r j := by
  let e :
      {sigma : {sigma : GenHashSupportTriple // sigma.1 l = j} //
          genSameOrbitExplicit sigma.1.1 (classRep r)} ≃
        {sigma // sigma ∈
          (genClassOrbit r).filter (fun sigma ↦ sigma l = j)} := {
    toFun sigma := ⟨sigma.1.1, by
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ _, sigma.2⟩
      · exact sigma.1.2⟩
    invFun sigma := by
      have hs := Finset.mem_filter.mp sigma.2
      have hsOrbit := Finset.mem_filter.mp hs.1
      exact ⟨⟨⟨sigma.1, orbit_support r sigma.1 hsOrbit.2⟩, hs.2⟩, hsOrbit.2⟩
    left_inv sigma := by
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      rfl
    right_inv sigma := by
      apply Subtype.ext
      rfl
  }
  calc
    Fintype.card
        {sigma : {sigma : GenHashSupportTriple // sigma.1 l = j} //
          genSameOrbitExplicit sigma.1.1 (classRep r)} =
        Nat.card
          {sigma // sigma ∈
            (genClassOrbit r).filter (fun sigma ↦ sigma l = j)} := by
      calc
        Fintype.card
            {sigma : {sigma : GenHashSupportTriple // sigma.1 l = j} //
              genSameOrbitExplicit sigma.1.1 (classRep r)} =
            Nat.card
              {sigma : {sigma : GenHashSupportTriple // sigma.1 l = j} //
                genSameOrbitExplicit sigma.1.1 (classRep r)} :=
          Nat.card_eq_fintype_card.symm
        _ = Nat.card
              {sigma // sigma ∈
                (genClassOrbit r).filter (fun sigma ↦ sigma l = j)} :=
          Nat.card_congr e
    _ = ((genClassOrbit r).filter (fun sigma ↦ sigma l = j)).card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ = genClassMarginalMultiplicity r j := orbit_coordinate_count r l j

theorem joint_table_marginal
    (base : Fin 10 → ℕ) (m : ℕ) (i : Fin 3) (j : Fin 9) :
    (∑ sigma : {sigma : GenHashSupportTriple // sigma.1 i = j},
      genHashTargetJointTable base m sigma.1) = genMarginalCount base m j := by
  calc
    (∑ sigma : {sigma : GenHashSupportTriple // sigma.1 i = j},
        genHashTargetJointTable base m sigma.1) =
        ∑ sigma : {sigma : GenHashSupportTriple // sigma.1 i = j},
          ∑ r : Fin 10,
            if genSameOrbitExplicit sigma.1.1 (classRep r) then
              base r * m else 0 := by
      apply Finset.sum_congr rfl
      intro sigma _
      simp only [genHashTargetJointTable, genJointMultiplicity,
        genProfileCount]
    _ = ∑ r : Fin 10,
        ∑ sigma : {sigma : GenHashSupportTriple // sigma.1 i = j},
          if genSameOrbitExplicit sigma.1.1 (classRep r) then
            base r * m else 0 := Finset.sum_comm
    _ = ∑ r : Fin 10, genClassMarginalMultiplicity r j * (base r * m) := by
      apply Finset.sum_congr rfl
      intro r _
      rw [sum_ite_const_eq_card
        (fun sigma : {sigma : GenHashSupportTriple // sigma.1 i = j} ↦
          genSameOrbitExplicit sigma.1.1 (classRep r)) (base r * m),
        class_card i j r]
    _ = genMarginalCount base m j := by
      simp only [genMarginalCount, genMarginalBaseCount, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro r _
      ring

end MME.StothersFourth.GeneralProfileArithmetic

open MME.StothersFourth.GeneralProfileArithmetic in
theorem solution :
    (∀ (r : Fin 10) (s : Fin 3) (j : Fin 9),
      ((MME.StothersFourth.genClassOrbit r).filter
          (fun sigma ↦ sigma s = j)).card =
        MME.StothersFourth.genClassMarginalMultiplicity r j) ∧
    (∀ base : Fin 10 → ℕ,
      ∑ j : Fin 9, MME.StothersFourth.genMarginalBaseCount base j =
        3 * MME.StothersFourth.genProfileScale base) ∧
    (∀ (base : Fin 10 → ℕ) (j : Fin 9),
      (MME.StothersFourth.genMarginalBaseCount base j : ℝ) =
        MME.StothersFourth.Q (fun i ↦ (base i : ℝ)) j) ∧
    (∀ (base : Fin 10 → ℕ) (m : ℕ) (i : Fin 3) (j : Fin 9),
      (∑ sigma : {sigma : MME.StothersFourth.GenHashSupportTriple //
          sigma.1 i = j},
        MME.StothersFourth.genHashTargetJointTable base m sigma.1) =
          MME.StothersFourth.genMarginalCount base m j) :=
  ⟨orbit_coordinate_count, marginal_base_sum, marginal_base_eq_Q,
    joint_table_marginal⟩
