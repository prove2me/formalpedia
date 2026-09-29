-- Prove2me | Theorems.Thm_ChebotarevDFT_exists_supported_vanishing
-- name    : ChebotarevDFT.exists_supported_vanishing
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:21:16.557301+00:00
-- url     : https://prove2.me/theorems/38e2b073-5672-433e-9878-65686eece052
-- title:
--   There is a nonzero function supported in `A` whose Fourier transform vanishes on any
-- statement:
--   There is a nonzero function supported in `A` whose Fourier transform vanishes on any
--   prescribed set `S` with `#S = #A - 1` (pure linear algebra: a square matrix with a zero
--   column is singular).
--
--   ```lean
--   theorem ChebotarevDFT.exists_supported_vanishing(A S : Finset (ZMod p)) (hcard : A.card = S.card + 1) :
--       ∃ f : ZMod p → ℂ, f ≠ 0 ∧ (∀ x, x ∉ A → f x = 0) ∧ ∀ s ∈ S, 𝓕 f s = 0 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/ChebotarevUncertainty.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/ChebotarevUncertainty.lean#L156

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

theorem ChebotarevDFT.exists_supported_vanishing(A S : Finset (ZMod p)) (hcard : A.card = S.card + 1) :
    ∃ f : ZMod p → ℂ, f ≠ 0 ∧ (∀ x, x ∉ A → f x = 0) ∧ ∀ s ∈ S, 𝓕 f s = 0 := by sorry
