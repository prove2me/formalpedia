-- Prove2me | Theorems.Thm_ChebotarevGeodesic_optimalExponent_torusCount_of_intValued
-- name    : ChebotarevGeodesic.optimalExponent_torusCount_of_intValued
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:25:33.757932+00:00
-- url     : https://prove2.me/theorems/23fd3718-f3ee-4f5c-8fcc-b67a319f17f4
-- title:
--   The same statement for a single torus: it recovers `optimalExponent_torusCount` from a
-- statement:
--   The same statement for a single torus: it recovers `optimalExponent_torusCount` from a
--   structural principle rather than from an explicit test sequence.
--
--   ```lean
--   theorem ChebotarevGeodesic.optimalExponent_torusCount_of_intValued{e : ℝ} (he : 1 < e) :
--       optimalExponent (fun x => (torusCount e x : ℝ))
--         (fun x => Real.log x / (2 * Real.log e)) = 0 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/ChebotarevGeodesicIntegrality.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/ChebotarevGeodesicIntegrality.lean#L178

-- Thm stub generated from Shared/ChebotarevGeodesicIntegrality.lean
import Mathlib
import Definitions.Def_Shared_ChebotarevGeodesic
import Definitions.Def_Shared_ChebotarevGeodesicOptimal
import Definitions.Def_Shared_ChebotarevGeodesicTorus
/-
# Integrality forces a non-negative optimal exponent

Continuation of `Shared.ChebotarevGeodesic`, `Shared.ChebotarevGeodesicOptimal` and
`Shared.ChebotarevGeodesicTorus`.

A geodesic counting function is *integer valued*, whereas the main terms occurring in the
prime geodesic and Chebotarev geodesic theorems (`li x`, `c·x^β`, `log x / (2 log ε)`, …) are
*continuous* and *unbounded*.  This file shows that this clash alone already forbids any
negative error exponent:

* `not_hasErrorExponent_of_intValued` : if `π` takes only integer values and `M` is continuous
  on `[1, ∞)` and tends to `+∞`, then `HasErrorExponent π M θ` fails for every `θ < 0`.
  The proof is an intermediate-value argument: choose `u` beyond which the error is `< 1/4`,
  use continuity of `M` to find `v ≥ u` with `M v = M u + 1/2`, and observe that
  `(π v - π u) - 1/2` is at distance `≥ 1/2` from `0` because `π v - π u ∈ ℤ`, while the two
  error bounds force it to be `< 1/2`.
* `optimalExponent_eq_zero_of_intValued` : consequently, an integer valued counting function
  with a bounded error has optimal exponent exactly `0`.
* `optimalExponent_torusFamily` : **conjecture C2 of `FUTURE_DIRECTIONS.md`.**  Every finite
  superposition of single-torus Chebotarev counting functions has optimal error exponent
  exactly `0`.  Hence the positive exponent `25/36` of the paper cannot be produced by any
  *finite* family of tori: it is a genuinely infinite (class-number) phenomenon.
* `le_optimalExponent_of_intValued` : for any integer valued counting function with continuous
  unbounded main term, `0 ≤ optimalExponent π M`; in particular no future improvement of the
  prime geodesic exponent can go below `0`.
-/


open Filter Set
open scoped Topology

open ChebotarevGeodesic

/-! ## The integrality obstruction -/




/-! ## Application: finite families of non-split tori -/

theorem ChebotarevGeodesic.optimalExponent_torusCount_of_intValued{e : ℝ} (he : 1 < e) :
    optimalExponent (fun x => (torusCount e x : ℝ))
      (fun x => Real.log x / (2 * Real.log e)) = 0 := by sorry
