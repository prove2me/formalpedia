-- Prove2me | solution 1 for FourierFA.poisson_summation
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T23:10:50.819488+00:00
-- url     : https://prove2.me/submissions/40c7bbd7-9a2b-4998-bc0d-7aeec5c32648

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













open FourierFA in
theorem solution(f : G → ℂ) :
    (Fintype.card G : ℂ) * ∑ x ∈ subFinset H, f x
      = ((subFinset H).card : ℂ) * ∑ ψ ∈ annih H, dft f ψ := by
  have hcard : (Fintype.card G : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero (α := G))
  have hf : ∀ x : G, (Fintype.card G : ℂ) * f x = ∑ ψ : AddChar G ℂ, ψ x * dft f ψ := by
    intro x
    conv_lhs => rw [← dft_inversion f]
    rw [idft, ← mul_assoc, mul_inv_cancel₀ hcard, one_mul]
  calc (Fintype.card G : ℂ) * ∑ x ∈ subFinset H, f x
      = ∑ x ∈ subFinset H, (Fintype.card G : ℂ) * f x := by rw [Finset.mul_sum]
    _ = ∑ x ∈ subFinset H, ∑ ψ : AddChar G ℂ, ψ x * dft f ψ :=
        Finset.sum_congr rfl fun x _ => hf x
    _ = ∑ ψ : AddChar G ℂ, (∑ x ∈ subFinset H, ψ x) * dft f ψ := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun ψ _ => by rw [Finset.sum_mul]
    _ = ∑ ψ : AddChar G ℂ, (if ψ ∈ annih H then ((subFinset H).card : ℂ) else 0) * dft f ψ := by
        exact Finset.sum_congr rfl fun ψ _ => by rw [sum_char_over_subgroup ψ]
    _ = ∑ ψ ∈ annih H, ((subFinset H).card : ℂ) * dft f ψ := by
        simp_rw [ite_mul, zero_mul]
        rw [Finset.sum_ite_mem, Finset.univ_inter]
    _ = ((subFinset H).card : ℂ) * ∑ ψ ∈ annih H, dft f ψ := by rw [Finset.mul_sum]
