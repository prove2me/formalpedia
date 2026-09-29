-- Prove2me | Theorems.Thm_ChebotarevDFT_dft_conv
-- name    : ChebotarevDFT.dft_conv
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:21:15.053981+00:00
-- url     : https://prove2.me/theorems/34ead44a-6a60-48b0-98f0-ca9b89440fa3
-- title:
--   The Fourier transform turns convolution into pointwise multiplication.
-- statement:
--   The Fourier transform turns convolution into pointwise multiplication.
--
--   ```lean
--   theorem ChebotarevDFT.dft_conv(f g : ZMod p → ℂ) (k : ZMod p) : 𝓕 (conv f g) k = 𝓕 f k * 𝓕 g k := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/ChebotarevCauchyDavenport.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/ChebotarevCauchyDavenport.lean#L26

-- Thm stub generated from Novelty/ChebotarevCauchyDavenport.lean
import Mathlib
import Definitions.Def_Novelty_ChebotarevCauchyDavenport
import Definitions.Def_Novelty_ChebotarevUncertainty
/-
# From Chebotarev to Cauchy–Davenport

A Fourier-analytic proof of the Cauchy–Davenport theorem, obtained from the prime-order
uncertainty principle `ChebotarevDFT.uncertainty` (which in turn rests on Chebotarev's theorem
about the nonsingularity of the square submatrices of the DFT matrix).

The route is: Chebotarev ⟹ uncertainty principle ⟹ Cauchy–Davenport, i.e. an algebraic
statement about cyclotomic fields controls an additive-combinatorial one.  (Mathlib contains a
different, combinatorial proof of Cauchy–Davenport; the point here is the bridge.)
-/

open ChebotarevDFT

open Finset Complex ZMod
open scoped ZMod Pointwise

variable {p : ℕ} [NeZero p]

/-! ## Convolution -/

theorem ChebotarevDFT.dft_conv(f g : ZMod p → ℂ) (k : ZMod p) : 𝓕 (conv f g) k = 𝓕 f k * 𝓕 g k := by sorry
