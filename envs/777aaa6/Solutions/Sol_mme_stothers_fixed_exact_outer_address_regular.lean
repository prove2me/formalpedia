-- Prove2me | solution 1 for mme_stothers_fixed_exact_outer_address_regular
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T18:52:22.687524+00:00
-- url     : https://prove2.me/submissions/60a3760b-9f3f-40fa-9f24-da3d89892869

import Definitions.Def_mme_stothers_fixed_outer_profile
import Mathlib.Tactic

open MME BigOperators
open MME.StothersFourth

set_option autoImplicit false
set_option maxRecDepth 100000

private theorem exactProfile_marginal_count
    (m : ℕ) (a : FixedExactOuterAddress m) (s : Fin 3) (j : Fin 9) :
    (Finset.univ.filter (fun k ↦ a.1 s k = j)).card =
      ∑ σ ∈ (Finset.univ.filter (fun σ : Fin 3 → Fin 9 ↦ σ s = j)),
        fixedJointMultiplicity m σ := by
  let types : Finset (Fin 3 → Fin 9) :=
    Finset.univ.filter (fun σ ↦ σ s = j)
  calc
    (Finset.univ.filter (fun k ↦ a.1 s k = j)).card =
        (Finset.univ.filter
          (fun k ↦ fixedAddressType a.1 k ∈ types)).card := by
      congr 1
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        types, fixedAddressType]
    _ = ∑ σ ∈ types,
        (Finset.univ.filter
          (fun k ↦ fixedAddressType a.1 k = σ)).card := by
      exact (Finset.sum_card_fiberwise_eq_card_filter
        Finset.univ types (fixedAddressType a.1)).symm
    _ = ∑ σ ∈ types, fixedJointMultiplicity m σ := by
      apply Finset.sum_congr rfl
      intro σ _hσ
      exact a.2 σ
    _ = ∑ σ ∈ (Finset.univ.filter
        (fun σ : Fin 3 → Fin 9 ↦ σ s = j)),
          fixedJointMultiplicity m σ := by rfl

private theorem orbit_sum_over_marginal
    (m : ℕ) (r : Fin 10) (s : Fin 3) (j : Fin 9) :
    (∑ σ ∈ (Finset.univ.filter (fun σ : Fin 3 → Fin 9 ↦ σ s = j)),
        if fixedSameOrbitExplicit σ (classRep r) then
          fixedProfileCount m r else 0) =
      fixedClassMarginalMultiplicity r j * fixedProfileCount m r := by
  let types : Finset (Fin 3 → Fin 9) :=
    Finset.univ.filter (fun σ ↦ σ s = j)
  calc
    (∑ σ ∈ types,
        if fixedSameOrbitExplicit σ (classRep r) then
          fixedProfileCount m r else 0) =
        ∑ σ ∈ types.filter
          (fun σ ↦ fixedSameOrbitExplicit σ (classRep r)),
            fixedProfileCount m r := by
      symm
      rw [Finset.sum_filter]
    _ = (types.filter
          (fun σ ↦ fixedSameOrbitExplicit σ (classRep r))).card *
          fixedProfileCount m r := by simp
    _ = ((fixedClassOrbit r).filter (fun σ ↦ σ s = j)).card *
          fixedProfileCount m r := by
      congr 2
      ext σ
      simp only [types, fixedClassOrbit, Finset.mem_filter,
        Finset.mem_univ, true_and]
      tauto
    _ = fixedClassMarginalMultiplicity r j *
          fixedProfileCount m r := by
      have h : ∀ r : Fin 10, ∀ s : Fin 3, ∀ j : Fin 9,
          ((fixedClassOrbit r).filter (fun σ ↦ σ s = j)).card =
            fixedClassMarginalMultiplicity r j := by
        decide
      rw [h r s j]

private theorem jointMultiplicity_sum_marginal
    (m : ℕ) (s : Fin 3) (j : Fin 9) :
    (∑ σ ∈ (Finset.univ.filter
      (fun σ : Fin 3 → Fin 9 ↦ σ s = j)),
        fixedJointMultiplicity m σ) = fixedMarginalCount m j := by
  let types : Finset (Fin 3 → Fin 9) :=
    Finset.univ.filter (fun σ ↦ σ s = j)
  calc
    (∑ σ ∈ types, fixedJointMultiplicity m σ) =
        ∑ r : Fin 10, ∑ σ ∈ types,
          if fixedSameOrbitExplicit σ (classRep r) then
            fixedProfileCount m r else 0 := by
      simp only [fixedJointMultiplicity]
      rw [Finset.sum_comm]
    _ = ∑ r : Fin 10,
        fixedClassMarginalMultiplicity r j * fixedProfileCount m r := by
      apply Finset.sum_congr rfl
      intro r _hr
      exact orbit_sum_over_marginal m r s j
    _ = m * ∑ r : Fin 10,
        fixedClassMarginalMultiplicity r j * fixedProfileBaseCount r := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _hr
      simp only [fixedProfileCount]
      ac_rfl
    _ = m * fixedMarginalBaseCount j := by
      congr 1
      symm
      fin_cases j <;>
        norm_num [fixedMarginalBaseCount, fixedClassMarginalMultiplicity,
          fixedProfileBaseCount, Fin.sum_univ_succ]
    _ = fixedMarginalCount m j := by rfl

private theorem exact_marginally_regular
    (m : ℕ) (a : FixedExactOuterAddress m) :
    FixedMarginallyRegular a.1 := by
  intro s j
  rw [exactProfile_marginal_count m a s j]
  exact jointMultiplicity_sum_marginal m s j

private theorem no_class_of_sum_ne_eight
    (σ : Fin 3 → Fin 9) (hσ : (∑ s, ((σ s).val : ℕ)) ≠ 8)
    (r : Fin 10) : ¬ fixedSameOrbitExplicit σ (classRep r) := by
  have h : ∀ σ : Fin 3 → Fin 9,
      (∑ s, ((σ s).val : ℕ)) ≠ 8 →
      ∀ r : Fin 10, ¬ fixedSameOrbitExplicit σ (classRep r) := by
    decide
  exact h σ hσ r

private theorem jointMultiplicity_eq_zero_of_sum_ne_eight
    (m : ℕ) (σ : Fin 3 → Fin 9)
    (hσ : (∑ s, ((σ s).val : ℕ)) ≠ 8) :
    fixedJointMultiplicity m σ = 0 := by
  simp [fixedJointMultiplicity, no_class_of_sum_ne_eight σ hσ]

private theorem exact_supported
    (m : ℕ) (a : FixedExactOuterAddress m) :
    FixedCoordinatewiseSupported a.1 := by
  intro k
  by_contra hsum
  let σ : Fin 3 → Fin 9 := fixedAddressType a.1 k
  have hk : k ∈ Finset.univ.filter
      (fun t ↦ fixedAddressType a.1 t = σ) := by
    simp [σ]
  have hpos : 0 <
      (Finset.univ.filter
        (fun t ↦ fixedAddressType a.1 t = σ)).card :=
    Finset.card_pos.mpr ⟨k, hk⟩
  have hσsum : (∑ s, ((σ s).val : ℕ)) ≠ 8 := by
    simpa [σ, fixedAddressType] using hsum
  rw [a.2 σ,
    jointMultiplicity_eq_zero_of_sum_ne_eight m σ hσsum] at hpos
  omega

theorem solution (m : ℕ) (a : FixedExactOuterAddress m) :
    FixedCoordinatewiseSupported a.1 ∧ FixedMarginallyRegular a.1 := by
  exact ⟨exact_supported m a, exact_marginally_regular m a⟩
