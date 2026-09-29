-- Prove2me | solution 1 for FourierFA.parseval
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T22:59:48.384104+00:00
-- url     : https://prove2.me/submissions/dfb7396d-de25-4db3-8057-c433f6e4ade0

-- Sol generated from Shared/FourierFiniteAbelian.lean
import Mathlib
import Definitions.Def_Shared_FourierFiniteAbelian
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
theorem solution(f g : G → ℂ) :
    ∑ ψ : AddChar G ℂ, dft f ψ * conj (dft g ψ)
      = (Fintype.card G : ℂ) * ∑ x, f x * conj (g x) := by
  have expand : ∀ ψ : AddChar G ℂ, dft f ψ * conj (dft g ψ)
      = ∑ x, ∑ y, (ψ y * conj (ψ x)) * (f x * conj (g y)) := by
    intro ψ
    rw [dft, dft, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    rw [map_mul, RCLike.conj_conj]
    ring
  have swap : ∑ ψ : AddChar G ℂ, ∑ x : G, ∑ y : G, (ψ y * conj (ψ x)) * (f x * conj (g y))
      = ∑ x : G, ∑ y : G, ∑ ψ : AddChar G ℂ, (ψ y * conj (ψ x)) * (f x * conj (g y)) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_comm
  have inner : ∀ x : G, ∑ y : G, ∑ ψ : AddChar G ℂ, (ψ y * conj (ψ x)) * (f x * conj (g y))
      = (Fintype.card G : ℂ) * (f x * conj (g x)) := by
    intro x
    have hy : ∀ y : G, ∑ ψ : AddChar G ℂ, (ψ y * conj (ψ x)) * (f x * conj (g y))
        = (if y = x then (Fintype.card G : ℂ) else 0) * (f x * conj (g y)) := by
      intro y
      rw [← Finset.sum_mul, sum_char_sub]
    simp_rw [hy]
    rw [Finset.sum_eq_single x]
    · simp
    · intro y _ hy'; simp [hy']
    · intro h; exact absurd (Finset.mem_univ x) h
  calc ∑ ψ : AddChar G ℂ, dft f ψ * conj (dft g ψ)
      = ∑ ψ : AddChar G ℂ, ∑ x : G, ∑ y : G, (ψ y * conj (ψ x)) * (f x * conj (g y)) :=
        Finset.sum_congr rfl fun ψ _ => expand ψ
    _ = ∑ x : G, ∑ y : G, ∑ ψ : AddChar G ℂ, (ψ y * conj (ψ x)) * (f x * conj (g y)) := swap
    _ = ∑ x : G, (Fintype.card G : ℂ) * (f x * conj (g x)) :=
        Finset.sum_congr rfl fun x _ => inner x
    _ = (Fintype.card G : ℂ) * ∑ x, f x * conj (g x) := by rw [Finset.mul_sum]
