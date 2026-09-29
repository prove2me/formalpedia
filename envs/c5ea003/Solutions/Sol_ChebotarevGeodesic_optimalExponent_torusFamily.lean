-- Prove2me | solution 1 for ChebotarevGeodesic.optimalExponent_torusFamily
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T21:01:51.816346+00:00
-- url     : https://prove2.me/submissions/bed65e56-4cff-4b61-935b-192bc9cf676d

-- Sol generated from Shared/ChebotarevGeodesicIntegrality.lean
import Mathlib
import Definitions.Def_Shared_ChebotarevGeodesic
import Definitions.Def_Shared_ChebotarevGeodesicOptimal
import Definitions.Def_Shared_ChebotarevGeodesicTorus
import Theorems.Thm_ChebotarevGeodesic_hasErrorExponent_torusFamily
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

/-- The main term of a finite family of tori is a positive multiple of `log`. -/
theorem torusFamily_main_eq {ι : Type*} (s : Finset ι) (e : ι → ℝ) {m : ℕ} (x : ℝ) :
    ∑ i ∈ s, (1 / (m : ℝ)) * (Real.log x / (2 * Real.log (e i)))
      = (∑ i ∈ s, (1 / (m : ℝ)) * (1 / (2 * Real.log (e i)))) * Real.log x := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- The coefficient of `log x` in the main term of a non-empty family of tori is positive. -/
theorem torusFamily_coeff_pos {ι : Type*} {s : Finset ι} {e : ι → ℝ} {m : ℕ}
    (hs : s.Nonempty) (he : ∀ i ∈ s, 1 < e i) (hm : 0 < m) :
    0 < ∑ i ∈ s, (1 / (m : ℝ)) * (1 / (2 * Real.log (e i))) := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  refine Finset.sum_pos (fun i hi => ?_) hs
  have hlog : 0 < Real.log (e i) := Real.log_pos (he i hi)
  positivity




open ChebotarevGeodesic in
theorem solution{ι : Type*} {s : Finset ι} {e : ι → ℝ} {m : ℕ} (a : ι → ℕ)
    (hs : s.Nonempty) (he : ∀ i ∈ s, 1 < e i) (hm : 0 < m) :
    optimalExponent (fun x => ∑ i ∈ s, (torusClassCount (e i) m (a i) x : ℝ))
      (fun x => ∑ i ∈ s, (1 / (m : ℝ)) * (Real.log x / (2 * Real.log (e i)))) = 0 := by
  set c : ℝ := ∑ i ∈ s, (1 / (m : ℝ)) * (1 / (2 * Real.log (e i))) with hcdef
  have hc : 0 < c := torusFamily_coeff_pos hs he hm
  have hMeq : (fun x => ∑ i ∈ s, (1 / (m : ℝ)) * (Real.log x / (2 * Real.log (e i))))
      = fun x => c * Real.log x := by
    funext x
    rw [hcdef]
    exact torusFamily_main_eq s e x
  refine optimalExponent_eq_zero_of_intValued ?_ ?_ ?_ ?_
  · intro x
    exact ⟨∑ i ∈ s, (torusClassCount (e i) m (a i) x : ℤ), by push_cast; ring⟩
  · rw [hMeq]
    refine continuousOn_const.mul (Real.continuousOn_log.mono fun z hz => ?_)
    have : (1 : ℝ) ≤ z := hz
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro hz0
    rw [hz0] at this
    linarith
  · rw [hMeq]
    exact Real.tendsto_log_atTop.const_mul_atTop hc
  · exact hasErrorExponent_torusFamily s e a he hm
