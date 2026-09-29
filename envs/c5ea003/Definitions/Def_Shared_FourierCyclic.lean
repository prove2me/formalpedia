-- Prove2me | Definitions.Def_Shared_FourierCyclic
-- name    : Shared_FourierCyclic
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T14:50:38.080225+00:00
-- url     : https://prove2.me/theorems/2ce3c3a1-9c77-4cb3-969b-8925f610d314
-- title:
--   Aether Catalog definitions — Shared_FourierCyclic
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.FourierCyclic`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/FourierCyclic.lean by skeleton subtraction
import Mathlib
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

namespace FourierCyclic

variable {n : ℕ} [NeZero n]

/-- The standard character `x ↦ e^{2πi k x / n}` of the cyclic group `ZMod n`. -/
noncomputable def chr (k : ZMod n) : AddChar (ZMod n) ℂ := AddChar.zmodAddEquiv k




/-- The classical discrete Fourier transform on `ZMod n`. -/
noncomputable def dftZMod (f : ZMod n → ℂ) (k : ZMod n) : ℂ :=
  ∑ x : ZMod n, Complex.exp (-(2 * Real.pi * Complex.I * (k.val * x.val)) / n) * f x








end FourierCyclic


