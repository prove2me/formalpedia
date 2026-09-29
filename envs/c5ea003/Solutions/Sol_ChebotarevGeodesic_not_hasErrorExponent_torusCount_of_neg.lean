-- Prove2me | solution 1 for ChebotarevGeodesic.not_hasErrorExponent_torusCount_of_neg
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T20:59:17.951803+00:00
-- url     : https://prove2.me/submissions/45e9bb19-a846-4c7b-8b53-df47461c3d54

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







/-! ## Counting a residue class -/


/-! ## The Chebotarev geodesic theorem for one torus -/



/-! ## A sharp Linnik-type bound for the least geodesic in a class -/


/-! ## Equidistribution of the geodesics of one torus -/



/-! ## Exact gaps, and finite families of tori -/




/-! ## Optimality of the exponent `0` -/



/-! ## A worked numerical example (`ε = 2`, `x = 100`, `m = 2`) -/





open ChebotarevGeodesic in
theorem solution{e : ℝ} (he : 1 < e) {θ : ℝ} (hθ : θ < 0) :
    ¬ HasErrorExponent (fun x => (torusCount e x : ℝ))
        (fun x => Real.log x / (2 * Real.log e)) θ := by
  intro h
  have he0 : 0 < e := lt_trans zero_lt_one he
  have hlog : 0 < Real.log e := log_pos_of_one_lt he
  obtain ⟨C, hC, X, hX, hb⟩ := h (-θ / 2) (by linarith)
  have hexp : θ + -θ / 2 = θ / 2 := by ring
  -- the test sequence
  have hpow : Tendsto (fun n : ℕ => e ^ (2 * n + 1)) atTop atTop := by
    have h1 : Tendsto (fun n : ℕ => e ^ n) atTop atTop := tendsto_pow_atTop_atTop_of_one_lt he
    exact h1.comp (Filter.tendsto_atTop_atTop.mpr fun b => ⟨b, fun n hn => by omega⟩)
  have hneg : Tendsto (fun t : ℝ => t ^ (θ / 2)) atTop (𝓝 0) := by
    have : θ / 2 = -(-(θ / 2)) := by ring
    rw [this]
    exact tendsto_rpow_neg_atTop (by linarith)
  have hcomp : Tendsto (fun n : ℕ => C * (e ^ (2 * n + 1) : ℝ) ^ (θ / 2)) atTop (𝓝 0) := by
    have := (hneg.comp hpow)
    simpa using this.const_mul C
  have hev1 : ∀ᶠ n : ℕ in atTop, C * (e ^ (2 * n + 1) : ℝ) ^ (θ / 2) < 1 / 2 :=
    hcomp.eventually (gt_mem_nhds (by norm_num))
  have hev2 : ∀ᶠ n : ℕ in atTop, X ≤ (e ^ (2 * n + 1) : ℝ) :=
    hpow.eventually_ge_atTop X
  obtain ⟨n, hn1, hn2⟩ := (hev1.and hev2).exists
  -- at `x = e^{2n+1}` the main term is `n + 1/2` and the count is `n`
  set x : ℝ := e ^ (2 * n + 1) with hxdef
  have hx1 : (1 : ℝ) ≤ x := le_trans hX hn2
  have hlogx : Real.log x = (2 * n + 1) * Real.log e := by
    rw [hxdef, Real.log_pow]; push_cast; ring
  have hmain : Real.log x / (2 * Real.log e) = (n : ℝ) + 1 / 2 := by
    rw [hlogx]
    field_simp
  have hcount : torusCount e x = n := by
    rw [torusCount, hmain]
    rw [Nat.floor_eq_iff (by positivity)]
    constructor
    · linarith
    · linarith
  have hbx : |(torusCount e x : ℝ) - Real.log x / (2 * Real.log e)| ≤ C * x ^ (θ / 2) := by
    have hb' := hb x hn2
    rwa [hexp] at hb'
  rw [hmain, hcount] at hbx
  have habs : |(n : ℝ) - ((n : ℝ) + 1 / 2)| = 1 / 2 := by
    rw [show (n : ℝ) - ((n : ℝ) + 1 / 2) = -(1 / 2) by ring, abs_neg, abs_of_pos (by norm_num)]
  rw [habs] at hbx
  linarith [hbx, hn1]
