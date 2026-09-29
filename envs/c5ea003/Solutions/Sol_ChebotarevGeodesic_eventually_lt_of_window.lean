-- Prove2me | solution 1 for ChebotarevGeodesic.eventually_lt_of_window
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T20:50:40.037255+00:00
-- url     : https://prove2.me/submissions/b4924030-f81e-4249-bad6-15107486b64a

-- Sol generated from Shared/ChebotarevGeodesicEffective.lean
import Mathlib
import Definitions.Def_Shared_ChebotarevGeodesic
import Theorems.Thm_ChebotarevGeodesic_eventually_rpow_lt_rpow
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
theorem solution{π : ℝ → ℝ} {θ β c lam : ℝ}
    (h : HasErrorExponent π (fun x => c * x ^ β) θ) (hc : 0 < c) (hβ : 0 < β) (hθβ : θ < β)
    (hlam : 1 < lam) :
    ∀ᶠ x in atTop, π x < π (lam * x) := by
  set ε : ℝ := (β - θ) / 2 with hεdef
  have hε : 0 < ε := by simp only [hεdef]; linarith
  set θ' : ℝ := θ + ε with hθ'def
  have hθ'β : θ' < β := by simp only [hθ'def, hεdef]; linarith
  obtain ⟨C, hC, X, hX, hb⟩ := h ε hε
  have hlam0 : (0 : ℝ) < lam := lt_trans zero_lt_one hlam
  have hlamβ : 1 < lam ^ β := Real.one_lt_rpow_iff_of_pos hlam0 |>.mpr (Or.inl ⟨hlam, hβ⟩)
  have hlamθ' : (0 : ℝ) < lam ^ θ' := Real.rpow_pos_of_pos hlam0 _
  have hdom := eventually_rpow_lt_rpow (a := θ') (b := β)
    (K := C * (lam ^ θ' + 1)) (L := c * (lam ^ β - 1)) hθ'β (by positivity) (by nlinarith)
  filter_upwards [hdom, eventually_ge_atTop X, eventually_ge_atTop (max X 1),
    eventually_gt_atTop (0 : ℝ)] with x hx hxX hxX1 hx0
  have hlamx : X ≤ lam * x := by nlinarith [le_trans (le_max_left X 1) hxX1]
  have h1 := hb x hxX
  have h2 := hb (lam * x) hlamx
  have e1 : (lam * x) ^ β = lam ^ β * x ^ β := Real.mul_rpow hlam0.le hx0.le
  have e2 : (lam * x) ^ θ' = lam ^ θ' * x ^ θ' := Real.mul_rpow hlam0.le hx0.le
  have hup : π x ≤ c * x ^ β + C * x ^ θ' := by
    have := abs_le.mp h1
    linarith [this.2]
  have hlow : c * (lam * x) ^ β - C * (lam * x) ^ θ' ≤ π (lam * x) := by
    have := abs_le.mp h2
    linarith [this.1]
  rw [e1, e2] at hlow
  -- combine: the gain `c(λ^β - 1)x^β` beats the two errors
  nlinarith [hx, hlow, hup, Real.rpow_pos_of_pos hx0 β, Real.rpow_pos_of_pos hx0 θ']
