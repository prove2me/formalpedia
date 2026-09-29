-- Prove2me | Theorems.Thm_ChebotarevDFT_uncertainty
-- name    : ChebotarevDFT.uncertainty
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:21:43.57842+00:00
-- url     : https://prove2.me/theorems/2cee8aaf-8766-437c-bb01-1a72d87338ac
-- title:
--   Tao's uncertainty principle for cyclic groups of prime order.
-- statement:
--   **Tao's uncertainty principle for cyclic groups of prime order.** If `Φ : ZMod p → ℂ` is
--   nonzero and `p` is prime, then the supports of `Φ` and of its discrete Fourier transform
--   together have at least `p + 1` elements.
--
--   ```lean
--   theorem ChebotarevDFT.uncertainty(hp : p.Prime) (Φ : ZMod p → ℂ) (hΦ : Φ ≠ 0) :
--       p + 1 ≤ (supp Φ).card + (supp (𝓕 Φ)).card := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/ChebotarevUncertainty.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/ChebotarevUncertainty.lean#L54

-- Thm stub generated from Novelty/ChebotarevUncertainty.lean
import Mathlib
import Definitions.Def_Novelty_ChebotarevDFT
import Definitions.Def_Novelty_ChebotarevUncertainty
/-
# Consequences of Chebotarev's theorem: the prime-order uncertainty principle

Building on `ChebotarevDFT.det_ne_zero` (every square submatrix of the `p × p` DFT matrix is
nonsingular for `p` prime) we derive:

* `ChebotarevDFT.uncertainty` : Tao's uncertainty principle, `#supp Φ + #supp (𝓕 Φ) ≥ p + 1`
  for every nonzero `Φ : ZMod p → ℂ`;
* `ChebotarevDFT.uncertainty_sharp_delta` : the bound is attained by a Dirac mass;
* `ChebotarevDFT.sparse_recovery` : a `k`-sparse signal on `ZMod p` is determined by *any*
  `2 * k` of its Fourier coefficients (exact recovery in compressed sensing);
* `ChebotarevDFT.singular_submatrix_of_composite` : for the composite modulus `4` the analogous
  statement fails, so primality is essential.
-/

open ChebotarevDFT

open Finset Matrix Complex ZMod
open scoped ZMod

variable {p : ℕ} [NeZero p]



/-! ## The standard additive character as a power of a primitive root -/



/-! ## The uncertainty principle -/

theorem ChebotarevDFT.uncertainty(hp : p.Prime) (Φ : ZMod p → ℂ) (hΦ : Φ ≠ 0) :
    p + 1 ≤ (supp Φ).card + (supp (𝓕 Φ)).card := by sorry
