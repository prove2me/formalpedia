-- Prove2me | solution 1 for ChebotarevGeodesic.sparseCount_bracket
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T20:52:18.830696+00:00
-- url     : https://prove2.me/submissions/407012e4-e49f-403e-a5bf-040c0530b396

-- Sol generated from Shared/ChebotarevGeodesicGaps.lean
import Mathlib
import Definitions.Def_Shared_ChebotarevGeodesic
import Definitions.Def_Shared_ChebotarevGeodesicGaps
import Definitions.Def_Shared_ChebotarevGeodesicTorus
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



/-! ## The critical window exponent is exactly `1 - (β - θ)`

The torus model above shows that *some* hypothesis on the size of the main term is needed.  We
now show that the numerical threshold `1 - (β - θ)` of `eventually_lt_of_additive_window` is
itself optimal, by exhibiting for every `θ ∈ [0,1)` a counting function with main term exactly
`x` and error exponent `θ` whose jumps are spaced `≍ x^{θ}` apart.  Writing `δ = 1 - θ`, the
example is the *`δ`-sparse counter*

  `sparseCount δ x = ⌊x^δ⌋^{1/δ}`,

which is constant on each interval `[n^{1/δ}, (n+1)^{1/δ})`. -/










open ChebotarevGeodesic in
theorem solution{δ x : ℝ} (hδ0 : 0 < δ) (hx : 1 ≤ x) :
    1 ≤ ⌊x ^ δ⌋₊ ∧ ((⌊x ^ δ⌋₊ : ℝ)) ^ (1 / δ) ≤ x ∧ x < ((⌊x ^ δ⌋₊ : ℝ) + 1) ^ (1 / δ) := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
  set p : ℝ := 1 / δ with hpdef
  have hp0 : 0 < p := by positivity
  have hxδ : (1 : ℝ) ≤ x ^ δ := Real.one_le_rpow hx hδ0.le
  have hn1 : 1 ≤ ⌊x ^ δ⌋₊ := Nat.le_floor (by exact_mod_cast hxδ)
  have hnonneg : (0 : ℝ) ≤ x ^ δ := Real.rpow_nonneg hx0.le _
  have hle : ((⌊x ^ δ⌋₊ : ℝ)) ≤ x ^ δ := Nat.floor_le hnonneg
  have hlt : x ^ δ < (⌊x ^ δ⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hxx : (x ^ δ) ^ p = x := by
    have h : δ * p = 1 := by rw [hpdef]; field_simp
    rw [← Real.rpow_mul hx0.le, h, Real.rpow_one]
  refine ⟨hn1, ?_, ?_⟩
  · calc ((⌊x ^ δ⌋₊ : ℝ)) ^ p ≤ (x ^ δ) ^ p := Real.rpow_le_rpow (by positivity) hle hp0.le
      _ = x := hxx
  · calc x = (x ^ δ) ^ p := hxx.symm
      _ < ((⌊x ^ δ⌋₊ : ℝ) + 1) ^ p := Real.rpow_lt_rpow hnonneg hlt hp0
