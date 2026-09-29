-- Prove2me | solution 1 for ChebotarevGeodesic.torusClassCount_pos_of_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T21:03:46.618774+00:00
-- url     : https://prove2.me/submissions/49000b3e-8b68-46af-9cf8-9afaf99ba123

-- Sol generated from Shared/ChebotarevGeodesicTorus.lean
import Mathlib
import Definitions.Def_Shared_ChebotarevGeodesic
import Definitions.Def_Shared_ChebotarevGeodesicOptimal
import Definitions.Def_Shared_ChebotarevGeodesicTorus
import Theorems.Thm_ChebotarevGeodesic_le_torusCount_iff
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
theorem solution{e : ℝ} (he : 1 < e) {m : ℕ} (hm : 0 < m) (a : ℕ) {x : ℝ}
    (hx : e ^ (2 * m) ≤ x) : 0 < torusClassCount e m a x := by
  classical
  have he1 : (1 : ℝ) ≤ e := he.le
  have hmod : a % m < m := Nat.mod_lt _ hm
  have hmodmod : (a % m) % m = a % m := Nat.mod_eq_of_lt hmod
  set k : ℕ := if a % m = 0 then m else a % m with hkdef
  have hk1 : 1 ≤ k := by
    simp only [hkdef]; split_ifs with h <;> omega
  have hkm : k ≤ m := by
    simp only [hkdef]; split_ifs with h <;> omega
  have hkmod : k % m = a % m := by
    simp only [hkdef]
    split_ifs with h
    · rw [Nat.mod_self, h]
    · exact hmodmod
  have hx1 : (1 : ℝ) ≤ x := le_trans (one_le_pow₀ he1) hx
  have hpow : e ^ (2 * k) ≤ x :=
    le_trans (pow_le_pow_right₀ he1 (by omega : 2 * k ≤ 2 * m)) hx
  have hkK : k ≤ torusCount e x := (le_torusCount_iff he hx1 k).mp hpow
  rw [torusClassCount, Finset.card_pos]
  exact ⟨k, by simp [Finset.mem_filter, Finset.mem_Icc, hk1, hkK, hkmod]⟩
