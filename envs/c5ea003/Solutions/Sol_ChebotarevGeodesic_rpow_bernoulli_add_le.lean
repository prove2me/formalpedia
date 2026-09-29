-- Prove2me | solution 1 for ChebotarevGeodesic.rpow_bernoulli_add_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T20:48:54.869861+00:00
-- url     : https://prove2.me/submissions/4d0853f3-701c-4c8b-8ca2-b9134b85115a

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
theorem solution{x h β : ℝ} (hx : 0 < x) (hh : 0 ≤ h) (hβ : 1 ≤ β) :
    x ^ β + β * x ^ (β - 1) * h ≤ (x + h) ^ β := by
  have hs0 : (0 : ℝ) ≤ h / x := by positivity
  have hs : (-1 : ℝ) ≤ h / x := by linarith
  have key := one_add_mul_self_le_rpow_one_add hs hβ
  have hxb : (0 : ℝ) < x ^ β := Real.rpow_pos_of_pos hx β
  have h1 : (x + h) ^ β = x ^ β * (1 + h / x) ^ β := by
    rw [← Real.mul_rpow hx.le (by positivity)]
    congr 1
    field_simp
  have h2 : x ^ (β - 1) = x ^ β / x := by rw [Real.rpow_sub hx, Real.rpow_one]
  rw [h1, h2]
  have h3 := mul_le_mul_of_nonneg_left key hxb.le
  calc x ^ β + β * (x ^ β / x) * h = x ^ β * (1 + β * (h / x)) := by field_simp
    _ ≤ x ^ β * (1 + h / x) ^ β := h3
