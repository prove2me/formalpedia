-- Prove2me | solution 1 for ChebotarevGeodesic.hasErrorExponent_torusClassCount
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T20:56:04.184931+00:00
-- url     : https://prove2.me/submissions/d9c86aaa-d3f8-4ee0-8e11-fbe7290c56f3

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

theorem torusCount_main_nonneg (he : 1 < e) (hx : 1 ≤ x) :
    0 ≤ Real.log x / (2 * Real.log e) := by
  have h1 : 0 ≤ Real.log x := Real.log_nonneg hx
  have h2 : 0 < Real.log e := log_pos_of_one_lt he
  positivity



/-- A floor is within `1` of its argument. -/
theorem abs_floor_sub_le_one {y : ℝ} (hy : 0 ≤ y) : |(⌊y⌋₊ : ℝ) - y| ≤ 1 := by
  have h1 : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le hy
  have h2 : y < (⌊y⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one y
  rw [abs_le]
  constructor <;> linarith



/-! ## Counting a residue class -/


/-! ## The Chebotarev geodesic theorem for one torus -/



/-! ## A sharp Linnik-type bound for the least geodesic in a class -/


/-! ## Equidistribution of the geodesics of one torus -/



/-! ## Exact gaps, and finite families of tori -/




/-! ## Optimality of the exponent `0` -/



/-! ## A worked numerical example (`ε = 2`, `x = 100`, `m = 2`) -/





open ChebotarevGeodesic in
theorem solution{e : ℝ} (he : 1 < e) {m : ℕ} (hm : 0 < m) (a : ℕ) :
    HasErrorExponent (fun x => (torusClassCount e m a x : ℝ))
      (fun x => (1 / m) * (Real.log x / (2 * Real.log e))) 0 := by
  intro ε hε
  refine ⟨4, by norm_num, 1, le_refl 1, fun x hx => ?_⟩
  set y : ℝ := Real.log x / (2 * Real.log e) with hy
  have hy0 : 0 ≤ y := torusCount_main_nonneg he hx
  set K : ℕ := torusCount e x with hK
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have h1 : |(torusClassCount e m a x : ℝ) - (K : ℝ) / m| ≤ 3 :=
    abs_card_residue_sub_le (a := a) hm
  have h2 : |(K : ℝ) - y| ≤ 1 := abs_floor_sub_le_one hy0
  have h3 : |(K : ℝ) / m - (1 / m) * y| ≤ 1 := by
    have e1 : (K : ℝ) / m - (1 / m) * y = ((K : ℝ) - y) / m := by ring
    rw [e1, abs_div, abs_of_pos hm0]
    calc |(K : ℝ) - y| / m ≤ 1 / m := by gcongr
      _ ≤ 1 := by
          rw [div_le_one hm0]; exact hm1
  have hxe : (1 : ℝ) ≤ x ^ (0 + ε) := by
    rw [zero_add]; exact Real.one_le_rpow hx hε.le
  have hsum : |(torusClassCount e m a x : ℝ) - (1 / m) * y| ≤ 4 := by
    calc |(torusClassCount e m a x : ℝ) - (1 / m) * y|
        ≤ |(torusClassCount e m a x : ℝ) - (K : ℝ) / m| + |(K : ℝ) / m - (1 / m) * y| := by
          exact abs_sub_le _ _ _
      _ ≤ 3 + 1 := add_le_add h1 h3
      _ = 4 := by norm_num
  nlinarith [hsum, hxe]
