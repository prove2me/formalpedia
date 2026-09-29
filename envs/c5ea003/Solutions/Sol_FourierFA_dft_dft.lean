-- Prove2me | solution 1 for FourierFA.dft_dft
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T23:10:42.864309+00:00
-- url     : https://prove2.me/submissions/8eeba981-7fbb-487d-a450-5d505dcb6b54

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
theorem solution(f : G → ℂ) (x : G) :
    dft (dft f) (AddChar.doubleDualEmb x) = (Fintype.card G : ℂ) * f (-x) := by
  classical
  rw [dft]
  have h1 : ∀ ψ : AddChar G ℂ, conj ((AddChar.doubleDualEmb x) ψ) * dft f ψ
      = ∑ y, conj (ψ x) * conj (ψ y) * f y := by
    intro ψ
    rw [dft, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [AddChar.doubleDualEmb_apply]
    ring
  simp_rw [h1]
  rw [Finset.sum_comm]
  have h2 : ∀ y : G, ∑ ψ : AddChar G ℂ, conj (ψ x) * conj (ψ y) * f y
      = (if x + y = 0 then (Fintype.card G : ℂ) else 0) * f y := by
    intro y
    rw [← Finset.sum_mul]
    congr 1
    have hc : ∀ ψ : AddChar G ℂ, conj (ψ x) * conj (ψ y) = conj (ψ (x + y)) := by
      intro ψ; rw [ψ.map_add_eq_mul, map_mul]
    simp_rw [hc]
    rw [← map_sum, AddChar.sum_apply_eq_ite]
    split_ifs <;> simp
  simp_rw [h2]
  rw [Finset.sum_eq_single (-x)]
  · simp
  · intro y _ hy
    have hne : x + y ≠ 0 := fun h => hy (by rw [← neg_eq_of_add_eq_zero_right h])
    simp [hne]
  · intro h; exact absurd (Finset.mem_univ (-x)) h
