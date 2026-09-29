-- Prove2me | Definitions.Def_Shared_ChebotarevGeodesicOptimal
-- name    : Shared_ChebotarevGeodesicOptimal
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T14:48:49.21912+00:00
-- url     : https://prove2.me/theorems/d462ce1d-e0ac-4765-a002-62684d1a2831
-- title:
--   Aether Catalog definitions — Shared_ChebotarevGeodesicOptimal
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.ChebotarevGeodesicOptimal`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/ChebotarevGeodesicOptimal.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Shared_ChebotarevGeodesic
/-
# The optimal exponent in the prime geodesic / Chebotarev geodesic theorem

Second research cycle on top of `Shared.ChebotarevGeodesic` and
`Shared.ChebotarevGeodesicSharpness`.

Papers on the prime geodesic theorem are a history of successive numerical exponents
(`3/4`, `35/48`, `7/10`, `71/102`, `25/36`, …).  This file makes the notion of "the exponent
of a counting function" a *bona fide* real number and proves that it behaves as one expects:

* `exponentSet π M` — the set of admissible exponents — is an **upper set** and is **closed
  from below**: `hasErrorExponent_of_forall_gt` shows that if every `θ' > θ` works, then `θ`
  itself works.  This is the (slightly surprising) reason the `ε` in "`25/36 + ε`" can never
  be removed by a limiting argument alone, yet the *exponent* `25/36` is attained.
* Consequently `exponentSet π M = Ici (optimalExponent π M)` whenever it is non-empty and
  bounded below (`exponentSet_eq_Ici`), so there is a genuine **optimal exponent**, and it is
  attained (`hasErrorExponent_optimalExponent`).
* The record chain becomes a chain of inequalities for one real number:
  `optimalExponent ≤ 25/36` (`optimalExponent_le_of_hasErrorExponent`).
* A logarithmic form of the estimate (`log_abs_error_le`), which is the shape in which the
  exponent is usually extracted numerically, and a lower bound for the optimal exponent
  coming from genuine oscillation of the error term (`le_optimalExponent_of_growth`).
-/


open Filter Set
open scoped Topology

namespace ChebotarevGeodesic

variable {π M : ℝ → ℝ} {θ : ℝ}

/-! ## Closure of the exponent set from below -/


/-- The set of admissible error exponents of the pair `(π, M)`. -/
def exponentSet (π M : ℝ → ℝ) : Set ℝ := {θ | HasErrorExponent π M θ}



/-! ## The optimal exponent -/

/-- The optimal (infimal, and by `hasErrorExponent_optimalExponent` attained) exponent. -/
noncomputable def optimalExponent (π M : ℝ → ℝ) : ℝ := sInf (exponentSet π M)

variable (π M)



variable {π M}



/-! ## Logarithmic form -/


/-! ## Lower bounds for the optimal exponent -/



/-! ## A computed optimal exponent -/



end ChebotarevGeodesic


