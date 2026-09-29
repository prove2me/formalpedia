-- Prove2me | solution 1 for ChebotarevGeodesic.tendsto_torusClassCount_ratio
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T21:03:45.881984+00:00
-- url     : https://prove2.me/submissions/0e8dee3a-db46-4b2f-ae0f-7f36ca55fdc4

-- Sol generated from Shared/ChebotarevGeodesicTorus.lean
import Mathlib
import Definitions.Def_Shared_ChebotarevGeodesic
import Definitions.Def_Shared_ChebotarevGeodesicOptimal
import Definitions.Def_Shared_ChebotarevGeodesicTorus
import Theorems.Thm_ChebotarevGeodesic_abs_card_residue_sub_le
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







/-! ## Counting a residue class -/


/-! ## The Chebotarev geodesic theorem for one torus -/



/-! ## A sharp Linnik-type bound for the least geodesic in a class -/


/-! ## Equidistribution of the geodesics of one torus -/

/-- The torus counting function tends to infinity. -/
theorem tendsto_torusCount_atTop {e : ℝ} (he : 1 < e) :
    Tendsto (fun x => (torusCount e x : ℝ)) atTop atTop := by
  have hlog : 0 < Real.log e := log_pos_of_one_lt he
  have hy : Tendsto (fun x : ℝ => Real.log x / (2 * Real.log e) - 1) atTop atTop := by
    have h1 : Tendsto (fun x : ℝ => Real.log x / (2 * Real.log e)) atTop atTop :=
      Real.tendsto_log_atTop.atTop_div_const (by positivity)
    exact (Filter.tendsto_atTop_add_const_right atTop (-1 : ℝ) h1).congr (fun x => by ring)
  refine tendsto_atTop_mono' atTop ?_ hy
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have h2 : Real.log x / (2 * Real.log e) < (torusCount e x : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  linarith


/-! ## Exact gaps, and finite families of tori -/




/-! ## Optimality of the exponent `0` -/



/-! ## A worked numerical example (`ε = 2`, `x = 100`, `m = 2`) -/





open ChebotarevGeodesic in
theorem solution{e : ℝ} (he : 1 < e) {m : ℕ} (hm : 0 < m) (a : ℕ) :
    Tendsto (fun x => (torusClassCount e m a x : ℝ) / (torusCount e x : ℝ)) atTop
      (𝓝 (1 / m)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hK := tendsto_torusCount_atTop he
  have hzero : Tendsto (fun x => 3 / (torusCount e x : ℝ)) atTop (𝓝 0) :=
    hK.const_div_atTop 3
  have hbound : ∀ᶠ x in atTop,
      ‖(torusClassCount e m a x : ℝ) / (torusCount e x : ℝ) - 1 / m‖
        ≤ 3 / (torusCount e x : ℝ) := by
    filter_upwards [hK.eventually_gt_atTop 0] with x hx
    have hne : ((torusCount e x : ℝ)) ≠ 0 := ne_of_gt hx
    have hkey : |((torusClassCount e m a x : ℝ)) - (torusCount e x : ℝ) / m| ≤ 3 :=
      abs_card_residue_sub_le (a := a) hm
    have he1 : (torusClassCount e m a x : ℝ) / (torusCount e x : ℝ) - 1 / m
        = ((torusClassCount e m a x : ℝ) - (torusCount e x : ℝ) / m) / (torusCount e x : ℝ) := by
      field_simp
    rw [Real.norm_eq_abs, he1, abs_div, abs_of_pos hx]
    gcongr
  have hlim : Tendsto
      (fun x => (torusClassCount e m a x : ℝ) / (torusCount e x : ℝ) - 1 / m) atTop (𝓝 0) :=
    squeeze_zero_norm' hbound hzero
  have hsum := hlim.add (tendsto_const_nhds (x := (1 : ℝ) / m) (f := atTop))
  simpa using hsum
