-- Prove2me | solution 1 for ChebotarevGeodesic.eventually_rpow_lt_rpow
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T20:48:54.223819+00:00
-- url     : https://prove2.me/submissions/bc81921a-e422-41a5-a8f3-449583054497

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



/-! ## The effective threshold -/





/-! ## Gaps: every window contains a new geodesic -/




open ChebotarevGeodesic in
theorem solution{a b K L : ℝ} (hab : a < b) (hK : 0 < K) (hL : 0 < L) :
    ∀ᶠ x in atTop, K * x ^ a < L * x ^ b := by
  have hpos : 0 < b - a := by linarith
  have hlim : Tendsto (fun x : ℝ => x ^ (-(b - a))) atTop (𝓝 0) := tendsto_rpow_neg_atTop hpos
  have hev := hlim.eventually (gt_mem_nhds (show (0 : ℝ) < L / (2 * K) by positivity))
  filter_upwards [hev, eventually_gt_atTop (0 : ℝ)] with x hxlt hx0
  have hsplit : x ^ a = x ^ (-(b - a)) * x ^ b := by
    rw [← Real.rpow_add hx0]; ring_nf
  have hxb : (0 : ℝ) < x ^ b := Real.rpow_pos_of_pos hx0 b
  have hkey : K * x ^ (-(b - a)) < L := by
    calc K * x ^ (-(b - a)) < K * (L / (2 * K)) := mul_lt_mul_of_pos_left hxlt hK
      _ = L / 2 := by field_simp
      _ < L := by linarith
  calc K * x ^ a = (K * x ^ (-(b - a))) * x ^ b := by rw [hsplit]; ring
    _ < L * x ^ b := mul_lt_mul_of_pos_right hkey hxb
