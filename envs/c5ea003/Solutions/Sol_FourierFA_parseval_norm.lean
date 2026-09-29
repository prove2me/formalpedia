-- Prove2me | solution 1 for FourierFA.parseval_norm
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T23:01:13.927892+00:00
-- url     : https://prove2.me/submissions/c0564bcb-ecb0-4623-8390-3d5a635e6621

-- Sol generated from Shared/FourierFiniteAbelian.lean
import Mathlib
import Definitions.Def_Shared_FourierFiniteAbelian
import Theorems.Thm_FourierFA_parseval
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







open FourierFA in
theorem solution(f : G → ℂ) :
    ∑ ψ : AddChar G ℂ, ‖dft f ψ‖ ^ 2 = (Fintype.card G : ℝ) * ∑ x, ‖f x‖ ^ 2 := by
  have h := parseval f f
  have hL : ∀ ψ : AddChar G ℂ, dft f ψ * conj (dft f ψ) = ((‖dft f ψ‖ ^ 2 : ℝ) : ℂ) := by
    intro ψ; rw [mul_comm, Complex.conj_mul']; norm_cast
  have hR : ∀ x : G, f x * conj (f x) = ((‖f x‖ ^ 2 : ℝ) : ℂ) := by
    intro x; rw [mul_comm, Complex.conj_mul']; norm_cast
  simp_rw [hL, hR] at h
  have hcast : ((∑ ψ : AddChar G ℂ, ‖dft f ψ‖ ^ 2 : ℝ) : ℂ)
      = (((Fintype.card G : ℝ) * ∑ x, ‖f x‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    push_cast at h
    exact h
  exact_mod_cast hcast
