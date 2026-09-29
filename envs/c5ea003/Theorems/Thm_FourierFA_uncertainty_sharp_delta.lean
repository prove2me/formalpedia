-- Prove2me | Theorems.Thm_FourierFA_uncertainty_sharp_delta
-- name    : FourierFA.uncertainty_sharp_delta
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:35:16.21715+00:00
-- url     : https://prove2.me/theorems/132e2d71-1360-43b9-8d3c-efb3ea8368f8
-- title:
--   The uncertainty bound is sharp: Dirac deltas attain equality.
-- statement:
--   The uncertainty bound is sharp: Dirac deltas attain equality.
--
--   ```lean
--   theorem FourierFA.uncertainty_sharp_delta(a : G) :
--       (supp (delta a)).card * (supp (dft (delta a))).card = Fintype.card G := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/FourierFiniteAbelian.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/FourierFiniteAbelian.lean#L402

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



/-! ## The convolution theorem -/


/-! ## Squaring the transform -/


/-! ## The Donoho–Stark uncertainty principle -/



/-! ## Sharpness -/

theorem FourierFA.uncertainty_sharp_delta(a : G) :
    (supp (delta a)).card * (supp (dft (delta a))).card = Fintype.card G := by sorry
