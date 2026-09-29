-- Prove2me | solution 1 for FourierFA.uncertainty_sharp_delta
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T23:12:30.39481+00:00
-- url     : https://prove2.me/submissions/18649894-55e1-444b-9b18-d3b624d8c1b7

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

/-! ## Definitions -/






/-! ## Orthogonality -/



/-! ## Linearity -/






/-! ## Fourier inversion -/







/-! ## Parseval / Plancherel -/



/-! ## The convolution theorem -/


/-! ## Squaring the transform -/


/-! ## The Donoho–Stark uncertainty principle -/



/-! ## Sharpness -/


@[simp] lemma dft_delta (a : G) (ψ : AddChar G ℂ) : dft (delta a) ψ = conj (ψ a) := by
  rw [dft, Finset.sum_eq_single a]
  · simp [delta]
  · intro b _ hb; simp [delta, hb]
  · intro h; exact absurd (Finset.mem_univ a) h

omit [AddCommGroup G] in
lemma supp_delta (a : G) : supp (delta a) = {a} := by
  ext x
  simp [mem_supp, delta]

lemma supp_dft_delta (a : G) : supp (dft (delta a)) = (Finset.univ : Finset (AddChar G ℂ)) := by
  ext ψ
  have : conj (ψ a) ≠ 0 := by
    have : ‖ψ a‖ = 1 := AddChar.norm_apply _ _
    simp only [ne_eq, map_eq_zero]
    intro h
    rw [h] at this
    simp at this
  simp [mem_supp, this]



open FourierFA in
theorem solution(a : G) :
    (supp (delta a)).card * (supp (dft (delta a))).card = Fintype.card G := by
  rw [supp_delta, supp_dft_delta, Finset.card_singleton, Finset.card_univ, one_mul,
    AddChar.card_eq]
