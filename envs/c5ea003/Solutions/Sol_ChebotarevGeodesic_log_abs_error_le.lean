-- Prove2me | solution 1 for ChebotarevGeodesic.log_abs_error_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T20:59:16.228322+00:00
-- url     : https://prove2.me/submissions/cbb76663-9f31-479f-871f-aa47be111f87

-- Sol generated from Shared/ChebotarevGeodesicOptimal.lean
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



variable {π M}



/-! ## Logarithmic form -/


/-! ## Lower bounds for the optimal exponent -/



/-! ## A computed optimal exponent -/




open ChebotarevGeodesic in
theorem solution(h : HasErrorExponent π M θ) (hθ : 0 ≤ θ) {θ' : ℝ} (hθ' : θ < θ') :
    ∀ᶠ x in atTop, Real.log |π x - M x| ≤ θ' * Real.log x := by
  set ε := (θ' - θ) / 2 with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  obtain ⟨C, hC, X, hX, hb⟩ := h ε hε
  have hCsmall : ∀ᶠ x in atTop, Real.log C ≤ ((θ' - θ - ε)) * Real.log x := by
    have hpos : 0 < θ' - θ - ε := by rw [hεdef]; linarith
    have hlog : Tendsto (fun x : ℝ => (θ' - θ - ε) * Real.log x) atTop atTop :=
      Filter.Tendsto.const_mul_atTop hpos Real.tendsto_log_atTop
    exact hlog.eventually_ge_atTop (Real.log C)
  filter_upwards [eventually_ge_atTop X, eventually_ge_atTop (1:ℝ), hCsmall]
    with x hxX hx1 hxC
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx1
  have hbound := hb x hxX
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx1
  rcases eq_or_lt_of_le (abs_nonneg (π x - M x)) with hz | hz
  · rw [← hz]
    simpa using mul_nonneg (by linarith : (0:ℝ) ≤ θ') hlogx
  · have h1 : Real.log |π x - M x| ≤ Real.log (C * x ^ (θ + ε)) :=
      Real.log_le_log hz hbound
    have h2 : Real.log (C * x ^ (θ + ε)) = Real.log C + (θ + ε) * Real.log x := by
      rw [Real.log_mul (ne_of_gt hC) (ne_of_gt (Real.rpow_pos_of_pos hx0 _)),
        Real.log_rpow hx0]
    rw [h2] at h1
    calc Real.log |π x - M x| ≤ Real.log C + (θ + ε) * Real.log x := h1
      _ ≤ (θ' - θ - ε) * Real.log x + (θ + ε) * Real.log x := by linarith
      _ = θ' * Real.log x := by ring
