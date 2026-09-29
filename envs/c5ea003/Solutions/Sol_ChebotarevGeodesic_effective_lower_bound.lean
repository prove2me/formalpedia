-- Prove2me | solution 1 for ChebotarevGeodesic.effective_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T20:48:53.000988+00:00
-- url     : https://prove2.me/submissions/cd21ff7b-29a3-46c4-94b1-0f6c0e2df874

-- Sol generated from Shared/ChebotarevGeodesicEffective.lean
import Mathlib
import Definitions.Def_Shared_ChebotarevGeodesic
/-
# Effective (Linnik-type) consequences of the Chebotarev geodesic theorem

Motivated by *"Chebotarev geodesic theorem: non-split case"*.  The qualitative corollary of a
Chebotarev-type asymptotic `π_C(x) = δ_C · li(x) + O(x^{θ+ε})` is that every conjugacy class
contains infinitely many primitive closed geodesics (this is `tendsto_atTop_of_hasErrorExponent`
in `ChebotarevGeodesic.lean`).  What the *effective* form of the theorem really provides is a
**threshold**: an explicit `X₀`, computed from the implied constant, beyond which the class
counting function is already at least half of its main term.  This is the geodesic analogue of
Linnik's theorem on the least prime in an arithmetic progression.

This file proves:

* `rpow_le_rpow_of_le_rpow_inv` : the elementary `rpow` threshold inequality;
* `eventually_rpow_lt_rpow` : `K·x^a < L·x^b` eventually, whenever `a < b`, `K, L > 0`;
* `effective_lower_bound` : an **explicit** threshold `max X₁ ((2C/c)^{2/(β-θ)})` beyond which
  `π x ≥ (c/2)·x^β`, given `|π - M| ≤ C x^{(θ+β)/2}` and `M x ≥ c x^β`;
* `effective_positivity` and `exists_effective_threshold` : the resulting positivity statement
  and its qualitative repackaging from `HasErrorExponent`;
* `effective_lower_bound_25_36` : the numerical instance for the exponent `25/36` of the paper
  (threshold `(2C/c)^{72/11}`);
* `eventually_lt_of_window` : *every* window `[x, λx]` with `λ > 1` eventually contains a new
  geodesic of the given class — a strengthening of "infinitely many" to a quantitative gap
  statement;
* `chebotarev_class_window_25_36` : the same for the exponent of the paper.
-/


open Finset Filter
open scoped Topology

open ChebotarevGeodesic

/-! ## Two elementary `rpow` facts -/

/-- If `x` is beyond the threshold `A^{1/δ}` then `x^δ` is beyond `A`. -/
theorem rpow_le_rpow_of_le_rpow_inv {A δ x : ℝ} (hA : 0 ≤ A) (hδ : 0 < δ)
    (hx : A ^ (1 / δ) ≤ x) : A ≤ x ^ δ := by
  have h0 : (0 : ℝ) ≤ A ^ (1 / δ) := Real.rpow_nonneg hA _
  calc A = (A ^ (1 / δ)) ^ δ := by
        rw [← Real.rpow_mul hA, one_div, inv_mul_cancel₀ hδ.ne', Real.rpow_one]
    _ ≤ x ^ δ := Real.rpow_le_rpow h0 hx hδ.le


/-! ## The effective threshold -/





/-! ## Gaps: every window contains a new geodesic -/




open ChebotarevGeodesic in
theorem solution{π M : ℝ → ℝ} {θ β c C X₁ : ℝ}
    (hc : 0 < c) (hC : 0 < C) (hθβ : θ < β) (hX₁ : 1 ≤ X₁)
    (hb : ∀ x ≥ X₁, |π x - M x| ≤ C * x ^ ((θ + β) / 2))
    (hM : ∀ x ≥ X₁, c * x ^ β ≤ M x) :
    ∀ x ≥ max X₁ ((2 * C / c) ^ (2 / (β - θ))), (c / 2) * x ^ β ≤ π x := by
  intro x hx
  have hxX₁ : X₁ ≤ x := le_trans (le_max_left _ _) hx
  have hxthr : (2 * C / c) ^ (2 / (β - θ)) ≤ x := le_trans (le_max_right _ _) hx
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one (le_trans hX₁ hxX₁)
  set δ : ℝ := (β - θ) / 2 with hδdef
  have hδ : 0 < δ := by simp only [hδdef]; linarith
  have hAδ : (2 * C / c) ≤ x ^ δ := by
    refine rpow_le_rpow_of_le_rpow_inv (by positivity) hδ ?_
    have hone : (1 : ℝ) / δ = 2 / (β - θ) := by
      simp only [hδdef]
      rw [one_div, inv_div]
    rw [hone]; exact hxthr
  -- the error is at most half the main term
  have hsplit : x ^ β = x ^ ((θ + β) / 2) * x ^ δ := by
    rw [← Real.rpow_add hx0]
    congr 1
    simp only [hδdef]; ring
  have hxmid : (0 : ℝ) < x ^ ((θ + β) / 2) := Real.rpow_pos_of_pos hx0 _
  have hCd : C ≤ (c / 2) * x ^ δ := by
    have h4 : (c / 2) * (2 * C / c) ≤ (c / 2) * x ^ δ :=
      mul_le_mul_of_nonneg_left hAδ (by positivity)
    have h5 : (c / 2) * (2 * C / c) = C := by field_simp
    linarith
  have herr : C * x ^ ((θ + β) / 2) ≤ (c / 2) * x ^ β := by
    rw [hsplit]
    calc C * x ^ ((θ + β) / 2) ≤ ((c / 2) * x ^ δ) * x ^ ((θ + β) / 2) :=
          mul_le_mul_of_nonneg_right hCd hxmid.le
      _ = (c / 2) * (x ^ ((θ + β) / 2) * x ^ δ) := by ring
  have h1 : |π x - M x| ≤ C * x ^ ((θ + β) / 2) := hb x hxX₁
  have h2 : c * x ^ β ≤ M x := hM x hxX₁
  have h3 : M x - π x ≤ C * x ^ ((θ + β) / 2) := by
    have := abs_le.mp h1
    linarith [this.1]
  linarith
