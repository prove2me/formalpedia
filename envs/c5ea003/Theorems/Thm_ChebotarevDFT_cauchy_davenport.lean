-- Prove2me | Theorems.Thm_ChebotarevDFT_cauchy_davenport
-- name    : ChebotarevDFT.cauchy_davenport
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:21:36.651308+00:00
-- url     : https://prove2.me/theorems/b92d57b1-e6d1-424d-a913-a9563384bd65
-- title:
--   Cauchy–Davenport, via the uncertainty principle.
-- statement:
--   **Cauchy–Davenport, via the uncertainty principle.** For nonempty subsets `A, B` of
--   `ZMod p` with `p` prime, `#(A + B) ≥ min p (#A + #B - 1)`.
--
--   ```lean
--   theorem ChebotarevDFT.cauchy_davenport(hp : p.Prime) (A B : Finset (ZMod p))
--       (hA : A.Nonempty) (hB : B.Nonempty) :
--       min p (A.card + B.card - 1) ≤ (A + B).card := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/ChebotarevCauchyDavenport.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/ChebotarevCauchyDavenport.lean#L64

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




/-! ## Two counting lemmas -/


/-! ## Cauchy–Davenport -/

theorem ChebotarevDFT.cauchy_davenport(hp : p.Prime) (A B : Finset (ZMod p))
    (hA : A.Nonempty) (hB : B.Nonempty) :
    min p (A.card + B.card - 1) ≤ (A + B).card := by sorry
