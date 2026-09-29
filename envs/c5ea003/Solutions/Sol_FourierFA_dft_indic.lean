-- Prove2me | solution 1 for FourierFA.dft_indic
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T23:08:51.614913+00:00
-- url     : https://prove2.me/submissions/adaa3536-b6f5-4844-a0bf-c32269644615

-- Sol generated from Shared/FourierSubgroupDuality.lean
import Mathlib
import Definitions.Def_Shared_FourierFiniteAbelian
import Definitions.Def_Shared_FourierSubgroupDuality
import Theorems.Thm_FourierFA_sum_char_over_subgroup
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
    dft (indic H) ψ = if ψ ∈ annih H then ((subFinset H).card : ℂ) else 0 := by
  have e1 : ∑ x ∈ subFinset H, conj (ψ x) * indic H x = ∑ x : G, conj (ψ x) * indic H x := by
    refine Finset.sum_subset (Finset.subset_univ _) ?_
    intro x _ hx
    have : indic H x = 0 := by
      simp only [indic, if_neg (fun hxH : x ∈ H => hx (mem_subFinset.2 hxH))]
    rw [this, mul_zero]
  have h1 : dft (indic H) ψ = ∑ x ∈ subFinset H, conj (ψ x) := by
    rw [dft, ← e1]
    refine Finset.sum_congr rfl fun x hx => ?_
    have : indic H x = 1 := by
      simp only [indic, if_pos (mem_subFinset.1 hx)]
    rw [this, mul_one]
  have h2 : ∀ x : G, conj (ψ x) = (-ψ) x := by
    intro x
    rw [AddChar.neg_apply', AddChar.inv_apply_eq_conj]
  have h3 : ((-ψ) ∈ annih H) ↔ (ψ ∈ annih H) := by
    simp only [mem_annih]
    constructor
    · intro h x hx
      have := h x hx
      rw [AddChar.neg_apply', inv_eq_one] at this
      exact this
    · intro h x hx
      rw [AddChar.neg_apply', h x hx, inv_one]
  rw [h1]
  simp_rw [h2]
  rw [sum_char_over_subgroup (-ψ)]
  by_cases h : ψ ∈ annih H
  · rw [if_pos (h3.2 h), if_pos h]
  · rw [if_neg (fun hc => h (h3.1 hc)), if_neg h]
