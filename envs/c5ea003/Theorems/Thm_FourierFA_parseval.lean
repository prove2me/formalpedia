-- Prove2me | Theorems.Thm_FourierFA_parseval
-- name    : FourierFA.parseval
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:33:34.313304+00:00
-- url     : https://prove2.me/theorems/6d1c2ef4-b7e4-4ab6-b014-79508ad3b873
-- title:
--   Parseval's theorem (sesquilinear form).
-- statement:
--   **Parseval's theorem** (sesquilinear form).
--
--   ```lean
--   theorem FourierFA.parseval(f g : G → ℂ) :
--       ∑ ψ : AddChar G ℂ, dft f ψ * conj (dft g ψ)
--         = (Fintype.card G : ℂ) * ∑ x, f x * conj (g x) := by sorry
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
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/FourierFiniteAbelian.lean#L177

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







/-! ## Parseval / Plancherel -/

theorem FourierFA.parseval(f g : G → ℂ) :
    ∑ ψ : AddChar G ℂ, dft f ψ * conj (dft g ψ)
      = (Fintype.card G : ℂ) * ∑ x, f x * conj (g x) := by sorry
