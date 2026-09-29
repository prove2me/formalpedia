-- Prove2me | Theorems.Thm_FourierFA_dft_injective
-- name    : FourierFA.dft_injective
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:34:45.295984+00:00
-- url     : https://prove2.me/theorems/be510a83-4192-4d4b-bf10-75e4efe9bdcd
-- title:
--   The DFT is injective.
-- statement:
--   The DFT is injective.
--
--   ```lean
--   theorem FourierFA.dft_injective: Function.Injective (dft : (G → ℂ) → AddChar G ℂ → ℂ) := by sorry
--
--
--
--
--   /-! ## Parseval / Plancherel -/
--
--
--
--   /-! ## The convolution theorem -/
--
--
--   /-! ## Squaring the transform -/
--
--
--   /-! ## The Donoho–Stark uncertainty principle -/
--
--
--
--   /-! ## Sharpness -/
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/FourierFiniteAbelian.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/FourierFiniteAbelian.lean#L125

-- Thm stub generated from Shared/FourierFiniteAbelian.lean
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

theorem FourierFA.dft_injective: Function.Injective (dft : (G → ℂ) → AddChar G ℂ → ℂ) := by sorry
