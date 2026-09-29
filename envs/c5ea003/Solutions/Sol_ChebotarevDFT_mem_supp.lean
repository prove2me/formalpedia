-- Prove2me | solution 1 for ChebotarevDFT.mem_supp
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T19:56:57.294497+00:00
-- url     : https://prove2.me/submissions/7fe034ae-df24-4b83-87ef-ed2c2c9aa15e

-- Sol generated from Novelty/ChebotarevUncertainty.lean
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








/-! ## Exact recovery of sparse signals -/



/-! ## Primality is essential -/



open ChebotarevDFT in
theorem solution{Φ : ZMod p → ℂ} {x : ZMod p} : x ∈ supp Φ ↔ Φ x ≠ 0 := by
  simp [supp]
