-- Prove2me | Theorems.Thm_ChebotarevGeodesic_not_hasErrorExponent_torusCount_of_neg
-- name    : ChebotarevGeodesic.not_hasErrorExponent_torusCount_of_neg
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:23:27.159976+00:00
-- url     : https://prove2.me/theorems/a32e5430-7af6-489e-a49c-7df3f66637c8
-- title:
--   Along the sequence `x = e^{2n+1}` the error of the torus count is exactly `1/2`; hence no
-- statement:
--   Along the sequence `x = e^{2n+1}` the error of the torus count is exactly `1/2`; hence no
--   *negative* error exponent is admissible: the exponent `0` is optimal.
--
--   ```lean
--   theorem ChebotarevGeodesic.not_hasErrorExponent_torusCount_of_neg{e : ℝ} (he : 1 < e) {θ : ℝ} (hθ : θ < 0) :
--       ¬ HasErrorExponent (fun x => (torusCount e x : ℝ))
--           (fun x => Real.log x / (2 * Real.log e)) θ := by sorry
--
--   /-! ## A worked numerical example (`ε = 2`, `x = 100`, `m = 2`) -/
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/ChebotarevGeodesicTorus.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/ChebotarevGeodesicTorus.lean#L335

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




/-! ## Optimality of the exponent `0` -/

theorem ChebotarevGeodesic.not_hasErrorExponent_torusCount_of_neg{e : ℝ} (he : 1 < e) {θ : ℝ} (hθ : θ < 0) :
    ¬ HasErrorExponent (fun x => (torusCount e x : ℝ))
        (fun x => Real.log x / (2 * Real.log e)) θ := by sorry
