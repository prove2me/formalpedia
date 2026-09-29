-- Prove2me | solution 1 for ChebotarevGeodesic.exists_effective_threshold
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T20:50:47.278406+00:00
-- url     : https://prove2.me/submissions/5af3012b-573e-4fc8-94a9-1e13ef94aef1

-- Sol generated from Shared/ChebotarevGeodesicEffective.lean
import Mathlib
import Definitions.Def_Shared_ChebotarevGeodesic
import Theorems.Thm_ChebotarevGeodesic_effective_lower_bound
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



/-! ## The effective threshold -/





/-! ## Gaps: every window contains a new geodesic -/




open ChebotarevGeodesic in
theorem solution{π M : ℝ → ℝ} {θ β c : ℝ}
    (h : HasErrorExponent π M θ) (hc : 0 < c) (hθβ : θ < β)
    (hM : ∀ᶠ x in atTop, c * x ^ β ≤ M x) :
    ∃ X₀ ≥ (1 : ℝ), ∀ x ≥ X₀, (c / 2) * x ^ β ≤ π x := by
  obtain ⟨C, hC, X, hX, hb⟩ := h ((β - θ) / 2) (by linarith)
  obtain ⟨X', hX'⟩ := eventually_atTop.mp hM
  set X₁ : ℝ := max (max X X') 1 with hX₁def
  have hX₁ : 1 ≤ X₁ := le_max_right _ _
  have hb' : ∀ x ≥ X₁, |π x - M x| ≤ C * x ^ ((θ + β) / 2) := by
    intro x hx
    have : X ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
    have hbx := hb x this
    have he : θ + (β - θ) / 2 = (θ + β) / 2 := by ring
    rwa [he] at hbx
  have hM' : ∀ x ≥ X₁, c * x ^ β ≤ M x := by
    intro x hx
    exact hX' x (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx)
  refine ⟨max X₁ ((2 * C / c) ^ (2 / (β - θ))), le_trans hX₁ (le_max_left _ _), ?_⟩
  exact effective_lower_bound hc hC hθβ hX₁ hb' hM'
