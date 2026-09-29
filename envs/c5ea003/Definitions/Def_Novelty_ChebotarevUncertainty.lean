-- Prove2me | Definitions.Def_Novelty_ChebotarevUncertainty
-- name    : Novelty_ChebotarevUncertainty
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:09:15.598588+00:00
-- url     : https://prove2.me/theorems/d10bdd34-6edf-4ec4-9e3d-06f9b0e3c74f
-- title:
--   Aether Catalog definitions — Novelty_ChebotarevUncertainty
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.ChebotarevUncertainty`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/ChebotarevUncertainty.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_ChebotarevDFT
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

namespace ChebotarevDFT

open Finset Matrix Complex ZMod
open scoped ZMod

variable {p : ℕ} [NeZero p]

/-- The support of a function on `ZMod p`. -/
noncomputable def supp (Φ : ZMod p → ℂ) : Finset (ZMod p) :=
  Finset.univ.filter fun x => Φ x ≠ 0


/-! ## The standard additive character as a power of a primitive root -/



/-! ## The uncertainty principle -/


/-! ## Sharpness -/

/-- The Dirac mass at `0`. -/
noncomputable def dirac (p : ℕ) : ZMod p → ℂ := fun x => if x = 0 then 1 else 0







/-! ## Exact recovery of sparse signals -/



/-! ## Primality is essential -/


end ChebotarevDFT


