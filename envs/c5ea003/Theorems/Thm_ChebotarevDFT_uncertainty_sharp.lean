-- Prove2me | Theorems.Thm_ChebotarevDFT_uncertainty_sharp
-- name    : ChebotarevDFT.uncertainty_sharp
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:22:01.116559+00:00
-- url     : https://prove2.me/theorems/e888ef5d-47a0-4de2-9d6f-f9a91e74ae52
-- title:
--   The uncertainty principle is sharp on every prescribed support.
-- statement:
--   **The uncertainty principle is sharp on every prescribed support.** For any nonempty
--   `A ⊆ ZMod p` there is a function whose support is exactly `A` and for which
--   `#supp f + #supp (𝓕 f) = p + 1`.
--
--   ```lean
--   theorem ChebotarevDFT.uncertainty_sharp(hp : p.Prime) (A : Finset (ZMod p)) (hA : A.Nonempty) :
--       ∃ f : ZMod p → ℂ, supp f = A ∧ (supp f).card + (supp (𝓕 f)).card = p + 1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/ChebotarevUncertainty.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/ChebotarevUncertainty.lean#L200

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


/-! ## Sharpness -/

theorem ChebotarevDFT.uncertainty_sharp(hp : p.Prime) (A : Finset (ZMod p)) (hA : A.Nonempty) :
    ∃ f : ZMod p → ℂ, supp f = A ∧ (supp f).card + (supp (𝓕 f)).card = p + 1 := by sorry
