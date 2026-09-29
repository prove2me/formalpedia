-- Prove2me | solution 1 for ChebotarevGeodesic.optimalExponent_torusCount_of_intValued
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T21:01:51.107887+00:00
-- url     : https://prove2.me/submissions/9305c9ce-d6ef-40ca-82db-16ade57dd194

-- Sol generated from Shared/ChebotarevGeodesicIntegrality.lean
import Mathlib
import Definitions.Def_Shared_ChebotarevGeodesic
import Definitions.Def_Shared_ChebotarevGeodesicOptimal
import Definitions.Def_Shared_ChebotarevGeodesicTorus
import Theorems.Thm_ChebotarevGeodesic_hasErrorExponent_torusCount
import Theorems.Thm_ChebotarevGeodesic_not_hasErrorExponent_of_intValued
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


/-- The optimal exponent of an integer valued counting function with continuous unbounded main
term is `≥ 0`. -/
theorem le_optimalExponent_of_intValued {pi M : ℝ → ℝ}
    (hint : ∀ x, ∃ k : ℤ, pi x = (k : ℝ))
    (hcont : ContinuousOn M (Set.Ici (1 : ℝ)))
    (hlim : Tendsto M atTop atTop)
    (hne : (exponentSet pi M).Nonempty) :
    0 ≤ optimalExponent pi M := by
  refine le_csInf hne fun θ hθ => ?_
  by_contra hlt
  exact not_hasErrorExponent_of_intValued (lt_of_not_ge hlt) hint hcont hlim hθ

/-- **The exponent `0` is optimal for every integer valued counting function with a bounded
error.** -/
theorem optimalExponent_eq_zero_of_intValued {pi M : ℝ → ℝ}
    (hint : ∀ x, ∃ k : ℤ, pi x = (k : ℝ))
    (hcont : ContinuousOn M (Set.Ici (1 : ℝ)))
    (hlim : Tendsto M atTop atTop)
    (h0 : HasErrorExponent pi M 0) :
    optimalExponent pi M = 0 := by
  have hmem : (0 : ℝ) ∈ exponentSet pi M := h0
  have hbdd : BddBelow (exponentSet pi M) := by
    refine ⟨0, fun θ hθ => ?_⟩
    by_contra hlt
    exact not_hasErrorExponent_of_intValued (lt_of_not_ge hlt) hint hcont hlim hθ
  exact le_antisymm (csInf_le hbdd hmem)
    (le_optimalExponent_of_intValued hint hcont hlim ⟨0, hmem⟩)

/-! ## Application: finite families of non-split tori -/






open ChebotarevGeodesic in
theorem solution{e : ℝ} (he : 1 < e) :
    optimalExponent (fun x => (torusCount e x : ℝ))
      (fun x => Real.log x / (2 * Real.log e)) = 0 := by
  have hlog : 0 < Real.log e := Real.log_pos he
  have hMeq : (fun x => Real.log x / (2 * Real.log e))
      = fun x => (1 / (2 * Real.log e)) * Real.log x := by
    funext x; ring
  refine optimalExponent_eq_zero_of_intValued ?_ ?_ ?_ (hasErrorExponent_torusCount he)
  · intro x
    exact ⟨(torusCount e x : ℤ), by push_cast; ring⟩
  · rw [hMeq]
    refine continuousOn_const.mul (Real.continuousOn_log.mono fun z hz => ?_)
    have hz1 : (1 : ℝ) ≤ z := hz
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro hz0
    rw [hz0] at hz1
    linarith
  · rw [hMeq]
    exact Real.tendsto_log_atTop.const_mul_atTop (by positivity)
