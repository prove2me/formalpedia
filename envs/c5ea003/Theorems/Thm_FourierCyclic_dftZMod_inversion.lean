-- Prove2me | Theorems.Thm_FourierCyclic_dftZMod_inversion
-- name    : FourierCyclic.dftZMod_inversion
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:34:15.569457+00:00
-- url     : https://prove2.me/theorems/7745804c-5280-44e6-b4d3-b3f05e1e0ee0
-- title:
--   Fourier inversion for the classical DFT on `ZMod n`.
-- statement:
--   **Fourier inversion** for the classical DFT on `ZMod n`.
--
--   ```lean
--   theorem FourierCyclic.dftZMod_inversion(f : ZMod n → ℂ) (x : ZMod n) :
--       f x = (n : ℂ)⁻¹ * ∑ k : ZMod n,
--         Complex.exp (2 * Real.pi * Complex.I * (k.val * x.val) / n) * dftZMod f k := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/FourierCyclic.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/FourierCyclic.lean#L70

-- Thm stub generated from Shared/FourierCyclic.lean
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

theorem FourierCyclic.dftZMod_inversion(f : ZMod n → ℂ) (x : ZMod n) :
    f x = (n : ℂ)⁻¹ * ∑ k : ZMod n,
      Complex.exp (2 * Real.pi * Complex.I * (k.val * x.val) / n) * dftZMod f k := by sorry
