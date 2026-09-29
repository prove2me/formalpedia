-- Prove2me | Theorems.Thm_ChebotarevGeodesic_torusCount_mul_sq
-- name    : ChebotarevGeodesic.torusCount_mul_sq
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:26:05.220989+00:00
-- url     : https://prove2.me/theorems/7a3795dd-700d-4d84-8a79-8d1359b88cdb
-- title:
--   The geodesics of one torus form a geometric progression of ratio `Îµ^2`.
-- statement:
--   **The geodesics of one torus form a geometric progression of ratio `Îµ^2`.**  Dilating the
--   norm bound by `Îµ^2` adds exactly one geodesic: an *exact* window statement, sharper than the
--   general `eventually_lt_of_window`.
--
--   ```lean
--   theorem ChebotarevGeodesic.torusCount_mul_sq{e x : ℝ} (he : 1 < e) (hx : 1 ≤ x) :
--       torusCount e (e ^ 2 * x) = torusCount e x + 1 := by sorry
--
--
--   /-! ## Optimality of the exponent `0` -/
--
--
--
--   /-! ## A worked numerical example (`ε = 2`, `x = 100`, `m = 2`) -/
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/ChebotarevGeodesicTorus.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/ChebotarevGeodesicTorus.lean#L296

-- Thm stub generated from Shared/ChebotarevGeodesicTorus.lean
import Mathlib
import Definitions.Def_Shared_ChebotarevGeodesic
import Definitions.Def_Shared_ChebotarevGeodesicOptimal
import Definitions.Def_Shared_ChebotarevGeodesicTorus
/-
# The Chebotarev geodesic theorem for a single non-split torus

Motivated by *"Chebotarev geodesic theorem: non-split case"*.  In the non-split (division
algebra) setting the closed geodesics of the quaternionic surface are indexed by the units of
the orders of the embedded quadratic fields — the **non-split tori** — and the length of the
geodesic attached to the `k`-th power of a fundamental unit `ε > 1` is `2k·log ε`.  Counting the
geodesics of one fixed torus of norm `≤ x` therefore amounts to counting the integers `k ≥ 1`
with `ε^{2k} ≤ x`, and a Chebotarev condition "the Frobenius class of the geodesic is `a`" for a
cyclic covering of degree `m` amounts to the congruence `k ≡ a (mod m)`.

Unlike the full spectral problem, *this* case is completely accessible, and we prove the
Chebotarev geodesic theorem for it **with the optimal exponent `0`** (bounded error) — a
strictly stronger statement than the paper's `25/36 + ε`, valid for a single torus:

* `torusCount_spec` : `{k ≥ 1 : ε^{2k} ≤ x} = Icc 1 (torusCount ε x)`, i.e. the counting
  function is exactly `⌊log x / (2 log ε)⌋`;
* `hasErrorExponent_torusCount` : the prime geodesic theorem for one torus with exponent `0`;
* `hasErrorExponent_torusClassCount` : **the Chebotarev geodesic theorem for one torus**:
  each residue class `a mod m` gets the density `1/m`, with bounded error, hence exponent `0`;
* `sum_torusClassCount` : the class counts add up to the total count (consistency of the
  Chebotarev statement with the prime geodesic theorem);
* `not_hasErrorExponent_torusCount_of_neg` and `optimalExponent_torusCount` : the exponent `0`
  is **optimal** — no negative exponent is admissible, because the fractional part of
  `log x / (2 log ε)` equals `1/2` along the sequence `x = ε^{2n+1}`;
* `hasErrorExponent_torusClassCount_25_36` : a fortiori the paper's exponent holds here.
-/


open Finset Filter
open scoped Topology

open ChebotarevGeodesic

/-! ## The counting function of one non-split torus -/




variable {e x : ℝ}








/-! ## Counting a residue class -/


/-! ## The Chebotarev geodesic theorem for one torus -/



/-! ## A sharp Linnik-type bound for the least geodesic in a class -/


/-! ## Equidistribution of the geodesics of one torus -/



/-! ## Exact gaps, and finite families of tori -/

theorem ChebotarevGeodesic.torusCount_mul_sq{e x : ℝ} (he : 1 < e) (hx : 1 ≤ x) :
    torusCount e (e ^ 2 * x) = torusCount e x + 1 := by sorry
