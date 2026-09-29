-- Prove2me | solution 1 for FourierCyclic.dftZMod_inversion
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T23:07:40.409876+00:00
-- url     : https://prove2.me/submissions/cb000e1e-482a-4e06-b913-eb4810cafaaa

-- Sol generated from Shared/FourierCyclic.lean
import Mathlib
import Definitions.Def_Shared_FourierCyclic
import Definitions.Def_Shared_FourierFiniteAbelian
/-
# The classical discrete Fourier transform on `ZMod n`

This file specialises the representation-theoretic Fourier transform of
`Catalog.Shared.FourierFiniteAbelian` to the cyclic group `ZMod n`, where the characters are the
`n`-th roots of unity `x ↦ e^{2πi k x / n}`.  We show that the abstract transform coincides with
the classical DFT matrix `F_{k,x} = e^{-2πi k x / n}` and transfer inversion, Parseval, the
convolution theorem and the uncertainty principle to that concrete setting.

Main results:

* `FourierCyclic.chr_apply` : the standard characters of `ZMod n` are the roots of unity.
* `FourierCyclic.dftZMod_eq` : the classical DFT equals the abstract DFT at the standard character.
* `FourierCyclic.dftZMod_inversion` : the classical inversion formula.
* `FourierCyclic.dftZMod_parseval` : `∑_k |f̂(k)|² = n * ∑_x |f(x)|²`.
* `FourierCyclic.dftZMod_conv` : the classical convolution theorem.
* `FourierCyclic.uncertainty_zmod` : `|supp f| * |supp f̂| ≥ n` for `f ≠ 0`.
-/


open Finset ComplexConjugate FourierFA
open scoped Real

open FourierCyclic

variable {n : ℕ} [NeZero n]


/-- The standard characters of `ZMod n` are exactly the roots of unity. -/
theorem chr_apply (k x : ZMod n) :
    chr k x = Complex.exp (2 * Real.pi * Complex.I * (k.val * x.val) / n) := by
  have h1 : (AddChar.zmod n k) x = Circle.exp (2 * Real.pi * ((k.val : ℝ) * (x.val : ℝ) / n)) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val (a := k), ← ZMod.natCast_zmod_val (a := x)]
    have := AddChar.zmod_intCast n (k.val : ℤ) (x.val : ℤ)
    push_cast at this ⊢
    exact this
  show ((AddChar.zmod n k x : Circle) : ℂ) = _
  rw [h1, Circle.coe_exp]
  push_cast
  ring_nf




/-- The classical DFT is the abstract DFT evaluated at the standard characters. -/
theorem dftZMod_eq (f : ZMod n → ℂ) (k : ZMod n) : dftZMod f k = dft f (chr k) := by
  rw [dftZMod, dft]
  refine Finset.sum_congr rfl fun x _ => ?_
  congr 1
  rw [chr_apply, ← Complex.exp_conj]
  congr 1
  simp only [map_div₀, map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.conj_natCast,
    map_ofNat]
  ring








open FourierCyclic in
theorem solution(f : ZMod n → ℂ) (x : ZMod n) :
    f x = (n : ℂ)⁻¹ * ∑ k : ZMod n,
      Complex.exp (2 * Real.pi * Complex.I * (k.val * x.val) / n) * dftZMod f k := by
  have hcard : Fintype.card (ZMod n) = n := ZMod.card n
  have h : idft (dft f) x = f x := by rw [dft_inversion]
  rw [idft, hcard] at h
  rw [← h]
  congr 1
  rw [← Equiv.sum_comp (AddChar.zmodAddEquiv (n := n)).toEquiv
      (fun ψ : AddChar (ZMod n) ℂ => ψ x * dft f ψ)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [dftZMod_eq]
  congr 1
  rw [← chr_apply]
  rfl
