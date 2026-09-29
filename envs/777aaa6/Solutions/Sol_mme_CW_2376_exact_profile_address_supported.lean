-- Prove2me | solution 1 for mme_CW_2376_exact_profile_address_supported
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T19:17:04.468373+00:00
-- url     : https://prove2.me/submissions/d03ca435-bd70-4792-bcea-8544df9c37d1

import Definitions.Def_mme_CW_2376_profile_induced_family

open MME

set_option autoImplicit false

private theorem profileMultiplicity_zero_of_sum_ne
    (m : ℕ) (σ : Fin 3 → Fin 5)
    (hsum : (σ 0).val + (σ 1).val + (σ 2).val ≠ 4) :
    cw2376ProfileMultiplicity m σ = 0 := by
  have hscalar : σ ∉ cw2376ScalarTypes := by
    intro h
    simp only [cw2376ScalarTypes, Finset.mem_insert,
      Finset.mem_singleton] at h
    rcases h with h | h | h <;>
      rw [h] at hsum <;>
      norm_num [cwSquareBlockType] at hsum
  have hrect : σ ∉ cw2376RectTypes := by
    intro h
    simp only [cw2376RectTypes, Finset.mem_insert,
      Finset.mem_singleton] at h
    rcases h with h | h | h | h | h | h <;>
      rw [h] at hsum <;>
      norm_num [cwSquareBlockType] at hsum
  have hcentral : σ ∉ cw2376CentralTypes := by
    intro h
    simp only [cw2376CentralTypes, Finset.mem_insert,
      Finset.mem_singleton] at h
    rcases h with h | h | h <;>
      rw [h] at hsum <;>
      norm_num [cwSquareBlockType] at hsum
  have hcoupled : σ ∉ cw2376CoupledTypes := by
    intro h
    simp only [cw2376CoupledTypes, Finset.mem_insert,
      Finset.mem_singleton] at h
    rcases h with h | h | h <;>
      rw [h] at hsum <;>
      norm_num [cwSquareBlockType] at hsum
  simp [cw2376ProfileMultiplicity, hscalar, hrect, hcentral, hcoupled]

theorem solution
    (m : ℕ) (a : CW2376ExactProfileAddress m) :
    CW2376CoordinatewiseSupported a.1 := by
  intro j
  by_contra hsum
  let σ : Fin 3 → Fin 5 := cw2376AddressType a.1 j
  have hzero : cw2376ProfileMultiplicity m σ = 0 := by
    apply profileMultiplicity_zero_of_sum_ne m σ
    simpa only [σ, cw2376AddressType] using hsum
  have hcard := a.2 σ
  rw [hzero] at hcard
  have hj : j ∈ Finset.univ.filter
      (fun r => cw2376AddressType a.1 r = σ) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, σ]
  have hpos : 0 < (Finset.univ.filter
      (fun r => cw2376AddressType a.1 r = σ)).card :=
    Finset.card_pos.mpr ⟨j, hj⟩
  omega
