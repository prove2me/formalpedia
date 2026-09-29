-- Prove2me | solution 1 for mme_stothers_general_exact_outer_address_regular
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-09-08T05:12:16.911526+00:00
-- url     : https://prove2.me/submissions/5a0cdb47-32c1-441f-a2f4-0839ad8d3a21

import Definitions.Def_mme_stothers_general_outer_profile
import Theorems.Thm_mme_stothers_general_outer_profile_arithmetic
import Mathlib.Tactic

open MME BigOperators
open MME.StothersFourth

set_option autoImplicit false
set_option maxRecDepth 100000

namespace MME.StothersFourth.GeneralProfileRegular

private theorem exactProfile_marginal_count
    (base : Fin 10 → ℕ) (m : ℕ) (a : GenExactOuterAddress base m)
    (s : Fin 3) (j : Fin 9) :
    (Finset.univ.filter (fun k ↦ a.1 s k = j)).card =
      ∑ sigma ∈ (Finset.univ.filter (fun sigma : Fin 3 → Fin 9 ↦ sigma s = j)),
        genJointMultiplicity base m sigma := by
  let types : Finset (Fin 3 → Fin 9) :=
    Finset.univ.filter (fun sigma ↦ sigma s = j)
  calc
    (Finset.univ.filter (fun k ↦ a.1 s k = j)).card =
        (Finset.univ.filter
          (fun k ↦ genAddressType a.1 k ∈ types)).card := by
      congr 1
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        types, genAddressType]
    _ = ∑ sigma ∈ types,
        (Finset.univ.filter
          (fun k ↦ genAddressType a.1 k = sigma)).card := by
      exact (Finset.sum_card_fiberwise_eq_card_filter
        Finset.univ types (genAddressType a.1)).symm
    _ = ∑ sigma ∈ types, genJointMultiplicity base m sigma := by
      apply Finset.sum_congr rfl
      intro sigma _hsigma
      exact a.2 sigma
    _ = ∑ sigma ∈ (Finset.univ.filter
        (fun sigma : Fin 3 → Fin 9 ↦ sigma s = j)),
          genJointMultiplicity base m sigma := by rfl

private theorem orbit_sum_over_marginal
    (base : Fin 10 → ℕ) (m : ℕ) (r : Fin 10) (s : Fin 3) (j : Fin 9) :
    (∑ sigma ∈ (Finset.univ.filter (fun sigma : Fin 3 → Fin 9 ↦ sigma s = j)),
        if genSameOrbitExplicit sigma (classRep r) then
          genProfileCount base m r else 0) =
      genClassMarginalMultiplicity r j * genProfileCount base m r := by
  let types : Finset (Fin 3 → Fin 9) :=
    Finset.univ.filter (fun sigma ↦ sigma s = j)
  calc
    (∑ sigma ∈ types,
        if genSameOrbitExplicit sigma (classRep r) then
          genProfileCount base m r else 0) =
        ∑ _sigma ∈ types.filter
          (fun sigma ↦ genSameOrbitExplicit sigma (classRep r)),
            genProfileCount base m r := by
      symm
      rw [Finset.sum_filter]
    _ = (types.filter
          (fun sigma ↦ genSameOrbitExplicit sigma (classRep r))).card *
          genProfileCount base m r := by simp
    _ = ((genClassOrbit r).filter (fun sigma ↦ sigma s = j)).card *
          genProfileCount base m r := by
      congr 2
      ext sigma
      simp only [types, genClassOrbit, Finset.mem_filter,
        Finset.mem_univ, true_and]
      tauto
    _ = genClassMarginalMultiplicity r j * genProfileCount base m r := by
      rw [mme_stothers_general_outer_profile_arithmetic.1 r s j]

private theorem jointMultiplicity_sum_marginal
    (base : Fin 10 → ℕ) (m : ℕ) (s : Fin 3) (j : Fin 9) :
    (∑ sigma ∈ (Finset.univ.filter
      (fun sigma : Fin 3 → Fin 9 ↦ sigma s = j)),
        genJointMultiplicity base m sigma) = genMarginalCount base m j := by
  let types : Finset (Fin 3 → Fin 9) :=
    Finset.univ.filter (fun sigma ↦ sigma s = j)
  calc
    (∑ sigma ∈ types, genJointMultiplicity base m sigma) =
        ∑ r : Fin 10, ∑ sigma ∈ types,
          if genSameOrbitExplicit sigma (classRep r) then
            genProfileCount base m r else 0 := by
      simp only [genJointMultiplicity]
      rw [Finset.sum_comm]
    _ = ∑ r : Fin 10,
        genClassMarginalMultiplicity r j * genProfileCount base m r := by
      apply Finset.sum_congr rfl
      intro r _hr
      exact orbit_sum_over_marginal base m r s j
    _ = genMarginalCount base m j := by
      simp only [genMarginalCount, genMarginalBaseCount, genProfileCount,
        Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro r _hr
      ring

private theorem no_class_of_sum_ne_eight
    (sigma : Fin 3 → Fin 9) (hsigma : (∑ s, ((sigma s).val : ℕ)) ≠ 8)
    (r : Fin 10) : ¬ genSameOrbitExplicit sigma (classRep r) := by
  have h : ∀ sigma : Fin 3 → Fin 9,
      (∑ s, ((sigma s).val : ℕ)) ≠ 8 →
      ∀ r : Fin 10, ¬ genSameOrbitExplicit sigma (classRep r) := by
    decide
  exact h sigma hsigma r

private theorem jointMultiplicity_eq_zero_of_sum_ne_eight
    (base : Fin 10 → ℕ) (m : ℕ) (sigma : Fin 3 → Fin 9)
    (hsigma : (∑ s, ((sigma s).val : ℕ)) ≠ 8) :
    genJointMultiplicity base m sigma = 0 := by
  simp [genJointMultiplicity, no_class_of_sum_ne_eight sigma hsigma]

theorem exact_marginally_regular
    (base : Fin 10 → ℕ) (m : ℕ) (a : GenExactOuterAddress base m) :
    GenMarginallyRegular a.1 := by
  intro s j
  rw [exactProfile_marginal_count base m a s j]
  exact jointMultiplicity_sum_marginal base m s j

theorem exact_supported
    (base : Fin 10 → ℕ) (m : ℕ) (a : GenExactOuterAddress base m) :
    GenCoordinatewiseSupported a.1 := by
  intro k
  by_contra hsum
  let sigma : Fin 3 → Fin 9 := genAddressType a.1 k
  have hk : k ∈ Finset.univ.filter
      (fun t ↦ genAddressType a.1 t = sigma) := by
    simp [sigma]
  have hpos : 0 <
      (Finset.univ.filter
        (fun t ↦ genAddressType a.1 t = sigma)).card :=
    Finset.card_pos.mpr ⟨k, hk⟩
  have hsigmasum : (∑ s, ((sigma s).val : ℕ)) ≠ 8 := by
    simpa [sigma, genAddressType] using hsum
  rw [a.2 sigma,
    jointMultiplicity_eq_zero_of_sum_ne_eight base m sigma hsigmasum] at hpos
  omega

end MME.StothersFourth.GeneralProfileRegular

theorem solution (base : Fin 10 → ℕ) (m : ℕ)
    (a : MME.StothersFourth.GenExactOuterAddress base m) :
    MME.StothersFourth.GenCoordinatewiseSupported a.1 ∧
      MME.StothersFourth.GenMarginallyRegular a.1 :=
  ⟨MME.StothersFourth.GeneralProfileRegular.exact_supported base m a,
    MME.StothersFourth.GeneralProfileRegular.exact_marginally_regular base m a⟩
