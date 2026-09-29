-- Prove2me | solution 1 for ChebotarevGeodesic.abs_card_residue_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T20:40:36.703934+00:00
-- url     : https://prove2.me/submissions/4bcbd728-7227-49d0-9617-e3b9afab2a21

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








/-! ## Counting a residue class -/


/-! ## The Chebotarev geodesic theorem for one torus -/



/-! ## A sharp Linnik-type bound for the least geodesic in a class -/


/-! ## Equidistribution of the geodesics of one torus -/



/-! ## Exact gaps, and finite families of tori -/




/-! ## Optimality of the exponent `0` -/



/-! ## A worked numerical example (`ε = 2`, `x = 100`, `m = 2`) -/





open ChebotarevGeodesic in
theorem solution{m a K : ℕ} (hm : 0 < m) :
    |((((Finset.Icc 1 K).filter (fun k => k % m = a % m)).card : ℝ)) - (K : ℝ) / m| ≤ 3 := by
  classical
  -- relate `Icc 1 K` to `range (K+1)`
  have hrange : Finset.range (K + 1) = insert 0 (Finset.Icc 1 K) := by
    ext k
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  have hnotmem : (0 : ℕ) ∉ Finset.Icc 1 K := by simp
  have hcount : ((Finset.range (K + 1)).filter (fun k => k % m = a % m)).card
      = ((Finset.Icc 1 K).filter (fun k => k % m = a % m)).card
        + (if 0 % m = a % m then 1 else 0) := by
    rw [hrange, Finset.filter_insert]
    by_cases h : 0 % m = a % m
    · rw [if_pos h, if_pos h, Finset.card_insert_of_notMem (by simp [hnotmem])]
    · rw [if_neg h, if_neg h, add_zero]
  -- Mathlib's exact count over `[0, K+1)`
  have hcnt : (K + 1).count (fun k => k ≡ a [MOD m])
      = (K + 1) / m + (if a % m < (K + 1) % m then 1 else 0) := Nat.count_modEq_card _ hm a
  have hcnt' : ((Finset.range (K + 1)).filter (fun k => k % m = a % m)).card
      = (K + 1) / m + (if a % m < (K + 1) % m then 1 else 0) := by
    rw [← hcnt, Nat.count_eq_card_filter_range]
    congr 1
  -- compare `(K+1)/m` (natural division) with `K/m` (real division)
  have hq : ((K + 1) / m : ℕ) * m + (K + 1) % m = K + 1 := Nat.div_add_mod' _ _
  have hr : (K + 1) % m < m := Nat.mod_lt _ hm
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hqR : (((K + 1) / m : ℕ) : ℝ) * m + (((K + 1) % m : ℕ) : ℝ) = (K : ℝ) + 1 := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) hq
  have hrR : (((K + 1) % m : ℕ) : ℝ) < m := by exact_mod_cast hr
  have hr0 : (0 : ℝ) ≤ (((K + 1) % m : ℕ) : ℝ) := Nat.cast_nonneg _
  have hqbound : |(((K + 1) / m : ℕ) : ℝ) - (K : ℝ) / m| ≤ 1 := by
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hq1 : (K : ℝ) / m ≤ (((K + 1) / m : ℕ) : ℝ) + 1 := by
      rw [div_le_iff₀ hm0]; nlinarith
    have hq2 : (((K + 1) / m : ℕ) : ℝ) - 1 ≤ (K : ℝ) / m := by
      rw [le_div_iff₀ hm0]; nlinarith
    rw [abs_le]
    constructor <;> linarith
  -- assemble
  have hA : (((Finset.Icc 1 K).filter (fun k => k % m = a % m)).card : ℝ)
      = ((((Finset.range (K + 1)).filter (fun k => k % m = a % m)).card : ℝ))
        - (if 0 % m = a % m then (1 : ℝ) else 0) := by
    rw [hcount]
    push_cast
    split_ifs <;> ring
  rw [hA, hcnt']
  push_cast
  have hind1 : (0 : ℝ) ≤ (if a % m < (K + 1) % m then (1 : ℝ) else 0) := by positivity
  have hind1' : (if a % m < (K + 1) % m then (1 : ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
  have hind2 : (0 : ℝ) ≤ (if 0 % m = a % m then (1 : ℝ) else 0) := by positivity
  have hind2' : (if 0 % m = a % m then (1 : ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
  rw [abs_le] at hqbound ⊢
  constructor <;> [linarith [hqbound.1, hqbound.2]; linarith [hqbound.1, hqbound.2]]
