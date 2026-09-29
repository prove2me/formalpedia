-- Prove2me | solution 1 for ChebotarevGeodesic.torusCount_no_short_gaps
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T21:03:48.215283+00:00
-- url     : https://prove2.me/submissions/ec1bb08d-bb9d-4dc8-9d7f-e36d46d56e5f

-- Sol generated from Shared/ChebotarevGeodesicGaps.lean
import Mathlib
import Definitions.Def_Shared_ChebotarevGeodesic
import Definitions.Def_Shared_ChebotarevGeodesicGaps
import Definitions.Def_Shared_ChebotarevGeodesicTorus
import Theorems.Thm_ChebotarevGeodesic_eventually_rpow_lt_rpow
import Theorems.Thm_ChebotarevGeodesic_le_torusCount_iff
/-
# Short-interval (additive window) gaps for Chebotarev geodesic counting functions

Motivated by *"Chebotarev geodesic theorem: non-split case"* and continuing the development in
`Shared.ChebotarevGeodesic`, `Shared.ChebotarevGeodesicEffective` and
`Shared.ChebotarevGeodesicTorus`.

`eventually_lt_of_window` (in `ChebotarevGeodesicEffective.lean`) proves the *multiplicative*
window statement: if `π x = c x^β + O(x^{θ+ε})` with `θ < β`, then every dilated window
`[x, λ x]`, `λ > 1`, eventually contains a new geodesic.  This file proves the much stronger
**additive** (short-interval) statement predicted by conjecture C4 of `FUTURE_DIRECTIONS.md`:

* `rpow_bernoulli_add_le` : the scaled Bernoulli inequality
  `x^β + β x^{β-1} h ≤ (x+h)^β` for `β ≥ 1`, `x > 0`, `h ≥ 0`;
* `eventually_lt_of_additive_window` : for every exponent `γ` with
  `1 - (β - θ) < γ ≤ 1` the interval `[x, x + x^{γ}]` eventually contains a point counted
  by `π`;
* `exists_additive_window_threshold` : the same statement in explicit `∃ X₀, ∀ x ≥ X₀` form;
* `chebotarev_gap_25_36` : the numerical instance of the paper — with main term `c·x` and
  exponent `25/36`, consecutive geodesics of a fixed conjugacy class are at distance
  `≪ x^{25/36 + ε}`;
* `torusCount_eq_of_mem_Ico`, `torusCount_no_short_gaps` : the *sharpness boundary*.  For the
  single non-split torus, whose main term is logarithmic rather than a positive power, the
  conclusion fails for **every** `γ < 1`: there are arbitrarily large `x` with no geodesic at
  all in `[x, x + x^{γ}]`.  So a power-size main term is not a technical convenience in
  `eventually_lt_of_additive_window`, it is exactly what makes short-interval gaps possible.
-/


open Finset Filter
open scoped Topology

open ChebotarevGeodesic

/-! ## A scaled Bernoulli inequality -/


/-! ## Geodesics in short intervals -/




/-! ## Sharpness: a logarithmic main term admits arbitrarily long gaps -/

/-- The counting function of a single non-split torus is constant on each interval
`[ε^{2k}, ε^{2k+2})`. -/
theorem torusCount_eq_of_mem_Ico {e : ℝ} (he : 1 < e) {k : ℕ} {y : ℝ}
    (h1 : e ^ (2 * k) ≤ y) (h2 : y < e ^ (2 * (k + 1))) :
    torusCount e y = k := by
  have he0 : (0 : ℝ) < e := lt_trans zero_lt_one he
  have hy1 : (1 : ℝ) ≤ y :=
    le_trans (one_le_pow₀ he.le) h1
  have hle : k ≤ torusCount e y := (le_torusCount_iff he hy1 k).mp h1
  have hnot : ¬ (k + 1 ≤ torusCount e y) := by
    intro hcon
    exact absurd ((le_torusCount_iff he hy1 (k + 1)).mpr hcon) (not_le.mpr h2)
  omega


/-! ## The critical window exponent is exactly `1 - (β - θ)`

The torus model above shows that *some* hypothesis on the size of the main term is needed.  We
now show that the numerical threshold `1 - (β - θ)` of `eventually_lt_of_additive_window` is
itself optimal, by exhibiting for every `θ ∈ [0,1)` a counting function with main term exactly
`x` and error exponent `θ` whose jumps are spaced `≍ x^{θ}` apart.  Writing `δ = 1 - θ`, the
example is the *`δ`-sparse counter*

  `sparseCount δ x = ⌊x^δ⌋^{1/δ}`,

which is constant on each interval `[n^{1/δ}, (n+1)^{1/δ})`. -/










open ChebotarevGeodesic in
theorem solution{e : ℝ} (he : 1 < e) {γ : ℝ} (hγ : γ < 1) (B : ℝ) :
    ∃ x, B ≤ x ∧ 1 ≤ x ∧ torusCount e (x + x ^ γ) = torusCount e x := by
  have he0 : (0 : ℝ) < e := lt_trans zero_lt_one he
  have hsq : (1 : ℝ) < e ^ 2 := by nlinarith
  -- eventually `x^γ < (e² - 1) x`, so `x + x^γ` stays below `e² x`
  have hdom : ∀ᶠ x : ℝ in atTop, 1 * x ^ γ < (e ^ 2 - 1) * x ^ (1 : ℝ) :=
    eventually_rpow_lt_rpow hγ one_pos (by linarith)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hdom
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (max (max N B) 1) hsq
  refine ⟨e ^ (2 * k), ?_, ?_, ?_⟩
  · exact le_trans (le_trans (le_max_right N B) (le_max_left _ _)) (by rw [pow_mul]; exact hk.le)
  · exact le_trans (le_max_right _ _) (by rw [pow_mul]; exact hk.le)
  · set x : ℝ := e ^ (2 * k) with hxdef
    have hxk : (e ^ 2) ^ k = x := by rw [hxdef, pow_mul]
    have hx1 : (1 : ℝ) ≤ x := le_trans (le_max_right _ _) (by rw [← hxk]; exact hk.le)
    have hxN : N ≤ x :=
      le_trans (le_trans (le_max_left N B) (le_max_left _ _)) (by rw [← hxk]; exact hk.le)
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx1
    have hgap := hN x hxN
    rw [one_mul, Real.rpow_one] at hgap
    have hupper : x + x ^ γ < e ^ (2 * (k + 1)) := by
      have : e ^ (2 * (k + 1)) = e ^ 2 * x := by rw [hxdef, ← pow_add]; ring_nf
      rw [this]
      nlinarith
    have hlower : e ^ (2 * k) ≤ x + x ^ γ := by
      have : (0 : ℝ) < x ^ γ := Real.rpow_pos_of_pos hx0 _
      simp only [← hxdef]; linarith
    rw [torusCount_eq_of_mem_Ico he hlower hupper,
      torusCount_eq_of_mem_Ico he (le_refl (e ^ (2 * k))) (by
        have : e ^ (2 * (k + 1)) = e ^ 2 * x := by rw [hxdef, ← pow_add]; ring_nf
        rw [this]; nlinarith)]
