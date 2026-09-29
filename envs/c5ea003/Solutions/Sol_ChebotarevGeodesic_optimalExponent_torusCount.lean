-- Prove2me | solution 1 for ChebotarevGeodesic.optimalExponent_torusCount
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T21:01:50.477092+00:00
-- url     : https://prove2.me/submissions/53a70cfb-3e8c-46a6-8a37-6be184ab3ca5

-- Sol generated from Shared/ChebotarevGeodesicTorus.lean
import Mathlib
import Definitions.Def_Shared_ChebotarevGeodesic
import Definitions.Def_Shared_ChebotarevGeodesicOptimal
import Definitions.Def_Shared_ChebotarevGeodesicTorus
import Theorems.Thm_ChebotarevGeodesic_hasErrorExponent_torusCount
import Theorems.Thm_ChebotarevGeodesic_not_hasErrorExponent_torusCount_of_neg
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



/-! ## A worked numerical example (`ε = 2`, `x = 100`, `m = 2`) -/





open ChebotarevGeodesic in
theorem solution{e : ℝ} (he : 1 < e) :
    optimalExponent (fun x => (torusCount e x : ℝ))
      (fun x => Real.log x / (2 * Real.log e)) = 0 := by
  have hmem : (0 : ℝ) ∈ exponentSet (fun x => (torusCount e x : ℝ))
      (fun x => Real.log x / (2 * Real.log e)) := hasErrorExponent_torusCount he
  have hbdd : BddBelow (exponentSet (fun x => (torusCount e x : ℝ))
      (fun x => Real.log x / (2 * Real.log e))) := by
    refine ⟨0, fun θ hθ => ?_⟩
    by_contra hlt
    exact not_hasErrorExponent_torusCount_of_neg he (lt_of_not_ge hlt) hθ
  refine le_antisymm (csInf_le hbdd hmem) ?_
  refine le_csInf ⟨0, hmem⟩ ?_
  intro θ hθ
  by_contra hlt
  exact not_hasErrorExponent_torusCount_of_neg he (lt_of_not_ge hlt) hθ
