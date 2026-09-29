-- Prove2me | Definitions.Def_Novelty_ChebotarevCauchyDavenport
-- name    : Novelty_ChebotarevCauchyDavenport
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:09:49.688465+00:00
-- url     : https://prove2.me/theorems/6b27a1ea-d895-4ede-87a7-83e5f8bd8e65
-- title:
--   Aether Catalog definitions — Novelty_ChebotarevCauchyDavenport
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.ChebotarevCauchyDavenport`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/ChebotarevCauchyDavenport.lean by skeleton subtraction
import Mathlib
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

namespace ChebotarevDFT

open Finset Complex ZMod
open scoped ZMod Pointwise

variable {p : ℕ} [NeZero p]

/-! ## Convolution -/

/-- Convolution of two functions on `ZMod p`. -/
noncomputable def conv (f g : ZMod p → ℂ) : ZMod p → ℂ := fun x => ∑ y, f y * g (x - y)



/-! ## Two counting lemmas -/


/-! ## Cauchy–Davenport -/


end ChebotarevDFT


