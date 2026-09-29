-- Prove2me | solution 1 for ChebotarevGeodesic.torusCount_mul_sq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T21:03:47.234228+00:00
-- url     : https://prove2.me/submissions/f6300a47-59b1-4bf2-b503-13bb298ee190

-- Sol generated from Shared/ChebotarevGeodesicTorus.lean
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

theorem log_pos_of_one_lt (he : 1 < e) : 0 < Real.log e := Real.log_pos he

theorem torusCount_main_nonneg (he : 1 < e) (hx : 1 ≤ x) :
    0 ≤ Real.log x / (2 * Real.log e) := by
  have h1 : 0 ≤ Real.log x := Real.log_nonneg hx
  have h2 : 0 < Real.log e := log_pos_of_one_lt he
  positivity






/-! ## Counting a residue class -/


/-! ## The Chebotarev geodesic theorem for one torus -/



/-! ## A sharp Linnik-type bound for the least geodesic in a class -/


/-! ## Equidistribution of the geodesics of one torus -/



/-! ## Exact gaps, and finite families of tori -/




/-! ## Optimality of the exponent `0` -/



/-! ## A worked numerical example (`ε = 2`, `x = 100`, `m = 2`) -/





open ChebotarevGeodesic in
theorem solution{e x : ℝ} (he : 1 < e) (hx : 1 ≤ x) :
    torusCount e (e ^ 2 * x) = torusCount e x + 1 := by
  have he0 : (0 : ℝ) < e := lt_trans zero_lt_one he
  have hlog : 0 < Real.log e := log_pos_of_one_lt he
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
  have hlogmul : Real.log (e ^ 2 * x) = 2 * Real.log e + Real.log x := by
    rw [Real.log_mul (by positivity) (ne_of_gt hx0), Real.log_pow]
    push_cast; ring
  have hy : Real.log (e ^ 2 * x) / (2 * Real.log e)
      = Real.log x / (2 * Real.log e) + 1 := by
    rw [hlogmul]
    field_simp
    ring
  rw [torusCount, torusCount, hy, Nat.floor_add_one (torusCount_main_nonneg he hx)]
