-- Prove2me | solution 1 for FourierFA.dft_conv
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T22:57:36.52198+00:00
-- url     : https://prove2.me/submissions/277b6067-cfd6-4574-9f1a-41b251e30d40

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
omit [DecidableEq G] in
theorem solution(f g : G → ℂ) (ψ : AddChar G ℂ) :
    dft (conv f g) ψ = dft f ψ * dft g ψ := by
  have hstep : dft (conv f g) ψ = ∑ x, ∑ y, conj (ψ x) * (f y * g (x - y)) := by
    rw [dft]
    exact Finset.sum_congr rfl fun x _ => by rw [conv, Finset.mul_sum]
  rw [hstep, Finset.sum_comm]
  have : ∀ y : G, ∑ x : G, conj (ψ x) * (f y * g (x - y))
      = (conj (ψ y) * f y) * dft g ψ := by
    intro y
    rw [dft, Finset.mul_sum]
    rw [← Equiv.sum_comp (Equiv.addRight y) (fun x => conj (ψ x) * (f y * g (x - y)))]
    refine Finset.sum_congr rfl fun z _ => ?_
    have hz : (Equiv.addRight y) z = z + y := rfl
    rw [hz]
    have : conj (ψ (z + y)) = conj (ψ z) * conj (ψ y) := by
      rw [ψ.map_add_eq_mul, map_mul]
    rw [this]
    simp [add_sub_cancel_right]
    ring
  simp_rw [this]
  rw [← Finset.sum_mul]
  rfl
