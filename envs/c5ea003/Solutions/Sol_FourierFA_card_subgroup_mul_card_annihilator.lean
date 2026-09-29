-- Prove2me | solution 1 for FourierFA.card_subgroup_mul_card_annihilator
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T23:10:42.256491+00:00
-- url     : https://prove2.me/submissions/268b3921-db54-44ed-8efc-8afba34de208

-- Sol generated from Shared/FourierSubgroupDuality.lean
import Mathlib
import Definitions.Def_Shared_FourierFiniteAbelian
import Definitions.Def_Shared_FourierSubgroupDuality
import Theorems.Thm_FourierFA_dft_indic
import Theorems.Thm_FourierFA_parseval_norm
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
lemma subFinset_nonempty : (subFinset H).Nonempty := ⟨0, mem_subFinset.2 H.zero_mem⟩

omit [DecidableEq G] in
lemma card_subFinset_pos : 0 < (subFinset H).card :=
  Finset.card_pos.2 subFinset_nonempty









open FourierFA in
theorem solution:
    (subFinset H).card * (annih H).card = Fintype.card G := by
  have hpar := parseval_norm (indic H)
  -- right-hand side
  have hR : ∑ x : G, ‖indic H x‖ ^ 2 = ((subFinset H).card : ℝ) := by
    have : ∀ x : G, ‖indic H x‖ ^ 2 = if x ∈ subFinset H then (1 : ℝ) else 0 := by
      intro x
      by_cases hx : x ∈ H
      · simp [indic, hx, mem_subFinset]
      · simp [indic, hx, mem_subFinset]
    simp_rw [this]
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one]
  -- left-hand side
  have hL : ∑ ψ : AddChar G ℂ, ‖dft (indic H) ψ‖ ^ 2
      = ((annih H).card : ℝ) * ((subFinset H).card : ℝ) ^ 2 := by
    have : ∀ ψ : AddChar G ℂ, ‖dft (indic H) ψ‖ ^ 2
        = if ψ ∈ annih H then ((subFinset H).card : ℝ) ^ 2 else 0 := by
      intro ψ
      rw [dft_indic]
      by_cases h : ψ ∈ annih H
      · simp [h]
      · simp [h]
    simp_rw [this]
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  rw [hL, hR] at hpar
  have hpos : (0 : ℝ) < ((subFinset H).card : ℝ) := by exact_mod_cast card_subFinset_pos
  have hmul : ((annih H).card : ℝ) * ((subFinset H).card : ℝ)
      = (Fintype.card G : ℝ) := by
    have h2 : ((annih H).card : ℝ) * ((subFinset H).card : ℝ) * ((subFinset H).card : ℝ)
        = (Fintype.card G : ℝ) * ((subFinset H).card : ℝ) := by
      calc ((annih H).card : ℝ) * ((subFinset H).card : ℝ) * ((subFinset H).card : ℝ)
          = ((annih H).card : ℝ) * ((subFinset H).card : ℝ) ^ 2 := by ring
        _ = (Fintype.card G : ℝ) * ((subFinset H).card : ℝ) := hpar
    exact mul_right_cancel₀ (ne_of_gt hpos) h2
  rw [mul_comm] at hmul
  exact_mod_cast hmul
