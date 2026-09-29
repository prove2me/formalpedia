-- Prove2me | Theorems.Thm_ChebotarevGeodesic_sum_torusClassCount
-- name    : ChebotarevGeodesic.sum_torusClassCount
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:25:34.139979+00:00
-- url     : https://prove2.me/theorems/6fccd631-b06d-4ea8-a3fc-e95d957a57c5
-- title:
--   The class counts sum to the total count: the Chebotarev statement for one torus is
-- statement:
--   The class counts sum to the total count: the Chebotarev statement for one torus is
--   consistent with the prime geodesic theorem for that torus.
--
--   ```lean
--   theorem ChebotarevGeodesic.sum_torusClassCount(e : ℝ) {m : ℕ} (hm : 0 < m) (x : ℝ) :
--       ∑ a ∈ Finset.range m, torusClassCount e m a x = torusCount e x := by sorry
--   /-! ## A sharp Linnik-type bound for the least geodesic in a class -/
--
--
--   /-! ## Equidistribution of the geodesics of one torus -/
--
--
--
--   /-! ## Exact gaps, and finite families of tori -/
--
--
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
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/ChebotarevGeodesicTorus.lean#L200

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

theorem ChebotarevGeodesic.sum_torusClassCount(e : ℝ) {m : ℕ} (hm : 0 < m) (x : ℝ) :
    ∑ a ∈ Finset.range m, torusClassCount e m a x = torusCount e x := by sorry
