-- Prove2me | solution 1 for FourierFA.uncertainty_eq_subgroup
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T23:12:29.662644+00:00
-- url     : https://prove2.me/submissions/c73bfcfe-579b-4e3e-b1ff-3e6a8b8d6834

-- Sol generated from Shared/FourierSubgroupDuality.lean
import Mathlib
import Definitions.Def_Shared_FourierFiniteAbelian
import Definitions.Def_Shared_FourierSubgroupDuality
import Theorems.Thm_FourierFA_card_subgroup_mul_card_annihilator
import Theorems.Thm_FourierFA_dft_indic
import Theorems.Thm_FourierFA_mem_supp
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

omit [DecidableEq G] in
lemma supp_indic : supp (indic H) = subFinset H := by
  ext x
  simp [mem_supp, indic, subFinset]



/-- The support of the Fourier transform of `1_H` is exactly the annihilator `H^⊥`. -/
theorem supp_dft_indic : supp (dft (indic H)) = annih H := by
  ext ψ
  rw [mem_supp, dft_indic]
  by_cases h : ψ ∈ annih H
  · simp [h, card_subFinset_pos.ne']
  · simp [h]





open FourierFA in
theorem solution:
    (supp (indic H)).card * (supp (dft (indic H))).card = Fintype.card G := by
  rw [supp_indic, supp_dft_indic]
  exact card_subgroup_mul_card_annihilator
