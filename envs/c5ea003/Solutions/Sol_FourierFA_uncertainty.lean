-- Prove2me | solution 1 for FourierFA.uncertainty
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T21:19:11.103923+00:00
-- url     : https://prove2.me/submissions/8f8aeb55-135c-4e68-8690-dad31d184666

-- Sol generated from Shared/FourierFiniteAbelian.lean
import Mathlib
import Definitions.Def_Shared_FourierFiniteAbelian
import Theorems.Thm_FourierFA_mem_supp
/-
# Fourier analysis on finite abelian groups

This file develops the discrete Fourier transform (DFT) on an arbitrary finite abelian
group `G`, viewed as the decomposition of the regular representation into the characters
of `G` (equivalently, as the expansion in the Pontryagin dual `AddChar G ℂ`).

Main results:

* `FourierFA.sum_char_sub` : the orthogonality relation `∑ ψ, ψ (x - y) = |G| ⬝ [x = y]`.
* `FourierFA.dft_inversion` : Fourier inversion `f = idft (dft f)`.
* `FourierFA.parseval` : `∑_ψ f̂ ψ * conj (ĝ ψ) = |G| * ∑_x f x * conj (g x)`.
* `FourierFA.parseval_norm` : `∑_ψ ‖f̂ ψ‖² = |G| * ∑_x ‖f x‖²`.
* `FourierFA.dft_conv` : the convolution theorem `(f ∗ g)^ = f̂ · ĝ`.
* `FourierFA.dft_injective`, `FourierFA.dftEquiv` : the DFT is a linear equivalence.
* `FourierFA.uncertainty` : the Donoho–Stark uncertainty principle
  `|supp f| * |supp f̂| ≥ |G|` for `f ≠ 0`.
* `FourierFA.uncertainty_sharp_delta` : the bound is attained (Dirac deltas).
* `FourierFA.sum_char_mul_conj` : orthogonality of characters summed over the group.
* `FourierFA.idft_inversion`, `FourierFA.dftEquiv` : `idft` is a two-sided inverse, so the DFT
  is a linear equivalence with explicit inverse.
* `FourierFA.dft_dft` : `F² = |G| ⬝ reflection`, via Pontryagin's canonical embedding.
-/


open Finset Fintype ComplexConjugate
open scoped BigOperators

open FourierFA

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
/-! ## The Donoho–Stark uncertainty principle -/

omit [DecidableEq G] in
private lemma dft_bound (f : G → ℂ) (M : ℝ) (hM : ∀ x, ‖f x‖ ≤ M) (ψ : AddChar G ℂ) :
    ‖dft f ψ‖ ≤ (supp f).card * M := by
  have h1 : dft f ψ = ∑ x ∈ supp f, conj (ψ x) * f x := by
    rw [dft]
    refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
    intro x _ hx
    have : f x = 0 := by
      by_contra h
      exact hx (mem_supp.2 h)
    simp [this]
  rw [h1]
  calc ‖∑ x ∈ supp f, conj (ψ x) * f x‖ ≤ ∑ x ∈ supp f, ‖conj (ψ x) * f x‖ :=
        norm_sum_le _ _
    _ = ∑ x ∈ supp f, ‖f x‖ := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [norm_mul, RCLike.norm_conj, AddChar.norm_apply, one_mul]
    _ ≤ ∑ _x ∈ supp f, M := Finset.sum_le_sum fun x _ => hM x
    _ = (supp f).card * M := by rw [Finset.sum_const, nsmul_eq_mul]

open FourierFA in
theorem solution(f : G → ℂ) (hf : f ≠ 0) :
    (Fintype.card G : ℕ) ≤ (supp f).card * (supp (dft f)).card := by
  classical
  -- pick a maximizer of `‖f ·‖`
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : G, f x₀ ≠ 0 := by
    by_contra h
    push_neg at h
    exact hf (funext h)
  have hne : (Finset.univ : Finset G).Nonempty := ⟨x₀, Finset.mem_univ _⟩
  obtain ⟨m, -, hm⟩ := Finset.exists_max_image (Finset.univ : Finset G) (fun x => ‖f x‖) hne
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = ‖f m‖ := ⟨_, rfl⟩
  have hMpos : 0 < M := by
    rw [hMdef]; exact lt_of_lt_of_le (norm_pos_iff.2 hx₀) (hm x₀ (Finset.mem_univ _))
  have hMall : ∀ x, ‖f x‖ ≤ M := by
    intro x; rw [hMdef]; exact hm x (Finset.mem_univ _)
  -- bound the Fourier coefficients
  have hFbound : ∀ ψ : AddChar G ℂ, ‖dft f ψ‖ ≤ (supp f).card * M := dft_bound f M hMall
  -- bound `M` back by inversion
  have hinv : f m = (Fintype.card G : ℂ)⁻¹ * ∑ ψ : AddChar G ℂ, ψ m * dft f ψ := by
    conv_lhs => rw [← dft_inversion f]
    rfl
  have hcardpos : (0 : ℝ) < (Fintype.card G : ℝ) := by
    exact_mod_cast Fintype.card_pos (α := G)
  have hsum : ∑ ψ : AddChar G ℂ, ψ m * dft f ψ
      = ∑ ψ ∈ supp (dft f), ψ m * dft f ψ := by
    refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
    intro ψ _ hψ
    have : dft f ψ = 0 := by
      by_contra h
      exact hψ (mem_supp.2 h)
    simp [this]
  have h2 : ‖∑ ψ ∈ supp (dft f), ψ m * dft f ψ‖
      ≤ (supp (dft f)).card * ((supp f).card * M) := by
    calc ‖∑ ψ ∈ supp (dft f), ψ m * dft f ψ‖
        ≤ ∑ ψ ∈ supp (dft f), ‖ψ m * dft f ψ‖ := norm_sum_le _ _
      _ = ∑ ψ ∈ supp (dft f), ‖dft f ψ‖ := by
          refine Finset.sum_congr rfl fun ψ _ => ?_
          rw [norm_mul, AddChar.norm_apply, one_mul]
      _ ≤ ∑ _ψ ∈ supp (dft f), ((supp f).card * M) :=
          Finset.sum_le_sum fun ψ _ => hFbound ψ
      _ = (supp (dft f)).card * ((supp f).card * M) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hM_le : M ≤ (Fintype.card G : ℝ)⁻¹ * ((supp (dft f)).card * ((supp f).card * M)) := by
    calc M = ‖f m‖ := hMdef
      _ = ‖(Fintype.card G : ℂ)⁻¹ * ∑ ψ ∈ supp (dft f), ψ m * dft f ψ‖ := by
          rw [← hsum, ← hinv]
      _ = (Fintype.card G : ℝ)⁻¹ * ‖∑ ψ ∈ supp (dft f), ψ m * dft f ψ‖ := by
          rw [norm_mul]; simp
      _ ≤ (Fintype.card G : ℝ)⁻¹ * ((supp (dft f)).card * ((supp f).card * M)) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
  -- conclude
  have key : (Fintype.card G : ℝ) ≤ (supp f).card * (supp (dft f)).card := by
    have h := mul_le_mul_of_nonneg_left hM_le (le_of_lt hcardpos)
    rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hcardpos), one_mul] at h
    have h' : (Fintype.card G : ℝ) * M ≤ ((supp f).card * (supp (dft f)).card) * M := by
      calc (Fintype.card G : ℝ) * M ≤ (supp (dft f)).card * ((supp f).card * M) := h
        _ = ((supp f).card * (supp (dft f)).card) * M := by ring
    exact le_of_mul_le_mul_right (by linarith [h']) hMpos
  exact_mod_cast key
