-- Prove2me | solution 1 for FourierFA.sum_char_over_subgroup
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T23:07:40.927384+00:00
-- url     : https://prove2.me/submissions/8c5068b7-a844-4c94-9ce2-ff4b13f4ba9c

-- Sol generated from Shared/FourierSubgroupDuality.lean
import Mathlib
import Definitions.Def_Shared_FourierFiniteAbelian
import Definitions.Def_Shared_FourierSubgroupDuality
/-
# Subgroups, annihilators and extremals of the uncertainty principle

Building on `Catalog.Shared.FourierFiniteAbelian`, this file studies the Fourier transform of
the indicator function of a subgroup `H ≤ G` of a finite abelian group.

Main results:

* `FourierFA.sum_char_over_subgroup` : `∑_{x ∈ H} ψ x = |H| ⬝ [ψ ∈ H^⊥]`.
* `FourierFA.dft_indic` : the Fourier transform of `1_H` is `|H| ⬝ 1_{H^⊥}`.
* `FourierFA.card_subgroup_mul_card_annihilator` : `|H| * |H^⊥| = |G|`, obtained *from Plancherel*
  rather than from Pontryagin duality of the quotient.
* `FourierFA.uncertainty_eq_subgroup` : subgroup indicators are extremal for the Donoho–Stark
  uncertainty principle, i.e. `|supp 1_H| * |supp (1_H)^| = |G|` exactly.
* `FourierFA.poisson_summation` : `|G| * ∑_{x ∈ H} f x = |H| * ∑_{ψ ∈ H^⊥} f̂ ψ`.
-/


open Finset Fintype ComplexConjugate

open FourierFA

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
  (H : AddSubgroup G) [DecidablePred (· ∈ H)]




variable {H}

omit [DecidableEq G] in
@[simp] lemma mem_subFinset {x : G} : x ∈ subFinset H ↔ x ∈ H := by simp [subFinset]

omit [DecidableEq G] in
@[simp] lemma mem_annih {ψ : AddChar G ℂ} : ψ ∈ annih H ↔ ∀ x ∈ H, ψ x = 1 := by
  simp [annih]











open FourierFA in
theorem solution(ψ : AddChar G ℂ) :
    ∑ x ∈ subFinset H, ψ x = if ψ ∈ annih H then ((subFinset H).card : ℂ) else 0 := by
  by_cases h : ψ ∈ annih H
  · rw [if_pos h]
    rw [Finset.sum_congr rfl (fun x hx => mem_annih.1 h x (mem_subFinset.1 hx))]
    simp
  · rw [if_neg h]
    rw [mem_annih] at h
    push_neg at h
    obtain ⟨x₀, hx₀H, hx₀⟩ := h
    -- translation by `x₀` permutes `H`
    have himg : (subFinset H).image (fun x => x₀ + x) = subFinset H := by
      refine Finset.eq_of_subset_of_card_le ?_ ?_
      · intro y hy
        simp only [Finset.mem_image] at hy
        obtain ⟨x, hx, rfl⟩ := hy
        exact mem_subFinset.2 (H.add_mem hx₀H (mem_subFinset.1 hx))
      · rw [Finset.card_image_of_injective _ (add_right_injective x₀)]
    have hre : ∑ x ∈ subFinset H, ψ (x₀ + x) = ∑ x ∈ subFinset H, ψ x := by
      conv_rhs => rw [← himg]
      rw [Finset.sum_image (fun a _ b _ hab => add_right_injective x₀ hab)]
    have hmul : ψ x₀ * ∑ x ∈ subFinset H, ψ x = ∑ x ∈ subFinset H, ψ x := by
      rw [Finset.mul_sum]
      simp_rw [← ψ.map_add_eq_mul]
      exact hre
    have hz : (ψ x₀ - 1) * ∑ x ∈ subFinset H, ψ x = 0 := by
      rw [sub_mul, one_mul, hmul, sub_self]
    rcases mul_eq_zero.1 hz with h1 | h2
    · exact absurd (sub_eq_zero.1 h1) hx₀
    · exact h2
