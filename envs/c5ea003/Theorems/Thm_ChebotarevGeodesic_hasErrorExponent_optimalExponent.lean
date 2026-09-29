-- Prove2me | Theorems.Thm_ChebotarevGeodesic_hasErrorExponent_optimalExponent
-- name    : ChebotarevGeodesic.hasErrorExponent_optimalExponent
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:21:22.653496+00:00
-- url     : https://prove2.me/theorems/cddf79f7-dd70-4f8f-aad9-d4c406de134d
-- title:
--   If some exponent works and the exponent set is bounded below, then the optimal exponent
-- statement:
--   If some exponent works and the exponent set is bounded below, then the optimal exponent
--   is itself admissible: the infimum is attained.
--
--   ```lean
--   theorem ChebotarevGeodesic.hasErrorExponent_optimalExponent(hne : (exponentSet π M).Nonempty) :
--       HasErrorExponent π M (optimalExponent π M) := by sorry
--
--   variable {π M}
--
--
--
--   /-! ## Logarithmic form -/
--
--
--   /-! ## Lower bounds for the optimal exponent -/
--
--
--
--   /-! ## A computed optimal exponent -/
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/ChebotarevGeodesicOptimal.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/ChebotarevGeodesicOptimal.lean#L64

-- Thm stub generated from Shared/ChebotarevGeodesicOptimal.lean
import Mathlib
import Definitions.Def_Shared_ChebotarevGeodesic
import Definitions.Def_Shared_ChebotarevGeodesicOptimal
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

open ChebotarevGeodesic

variable {π M : ℝ → ℝ} {θ : ℝ}

/-! ## Closure of the exponent set from below -/





/-! ## The optimal exponent -/


variable (π M)

theorem ChebotarevGeodesic.hasErrorExponent_optimalExponent(hne : (exponentSet π M).Nonempty) :
    HasErrorExponent π M (optimalExponent π M) := by sorry
