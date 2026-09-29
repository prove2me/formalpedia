-- Prove2me | solution 1 for ChebotarevGeodesic.sparseCount_abs_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T20:54:27.794729+00:00
-- url     : https://prove2.me/submissions/5f610f6d-5f52-4a5b-a173-885bc2355c3a

-- Sol generated from Shared/ChebotarevGeodesicGaps.lean
import Mathlib
import Definitions.Def_Shared_ChebotarevGeodesic
import Definitions.Def_Shared_ChebotarevGeodesicGaps
import Definitions.Def_Shared_ChebotarevGeodesicTorus
import Theorems.Thm_ChebotarevGeodesic_rpow_sub_bernoulli_le
import Theorems.Thm_ChebotarevGeodesic_sparseCount_bracket
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
theorem solution{δ x : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hx : 1 ≤ x) :
    |sparseCount δ x - x| ≤ (1 / δ) * 2 ^ (1 / δ - 1) * x ^ (1 - δ) := by
  obtain ⟨hn1, hle, hlt⟩ := sparseCount_bracket hδ0 hx
  set p : ℝ := 1 / δ with hpdef
  have hp0 : 0 < p := by positivity
  have hp : 1 ≤ p := by rw [hpdef, le_div_iff₀ hδ0]; linarith
  set n : ℝ := ((⌊x ^ δ⌋₊ : ℕ) : ℝ) with hndef
  have hn1' : (1 : ℝ) ≤ n := by rw [hndef]; exact_mod_cast hn1
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1'
  have hb := rpow_sub_bernoulli_le (v := n + 1) (h := 1) (p := p) (by linarith) (by linarith) hp
  have hsimp : (n + 1 - 1 : ℝ) = n := by ring
  rw [hsimp, mul_one] at hb
  have hpe : p * (1 - δ) = p - 1 := by rw [hpdef]; field_simp
  have h21 : (n + 1) ^ (p - 1) ≤ 2 ^ (p - 1) * n ^ (p - 1) := by
    calc (n + 1) ^ (p - 1) ≤ (2 * n) ^ (p - 1) :=
          Real.rpow_le_rpow (by linarith) (by linarith) (by linarith)
      _ = 2 ^ (p - 1) * n ^ (p - 1) := Real.mul_rpow (by norm_num) hn0.le
  have hnx : n ^ (p - 1) ≤ x ^ (1 - δ) := by
    have h1 : (n ^ p) ^ (1 - δ) = n ^ (p - 1) := by rw [← Real.rpow_mul hn0.le, hpe]
    calc n ^ (p - 1) = (n ^ p) ^ (1 - δ) := h1.symm
      _ ≤ x ^ (1 - δ) := Real.rpow_le_rpow (Real.rpow_nonneg hn0.le _) hle (by linarith)
  have h2pos : (0 : ℝ) < 2 ^ (p - 1) := Real.rpow_pos_of_pos (by norm_num) _
  have hfinal : x - n ^ p ≤ p * (2 ^ (p - 1) * x ^ (1 - δ)) := by
    have hstep : x - n ^ p ≤ p * (n + 1) ^ (p - 1) := by linarith [hlt.le]
    have hmid : (n + 1) ^ (p - 1) ≤ 2 ^ (p - 1) * x ^ (1 - δ) :=
      le_trans h21 (mul_le_mul_of_nonneg_left hnx h2pos.le)
    calc x - n ^ p ≤ p * (n + 1) ^ (p - 1) := hstep
      _ ≤ p * (2 ^ (p - 1) * x ^ (1 - δ)) := mul_le_mul_of_nonneg_left hmid hp0.le
  have hsc : sparseCount δ x = n ^ p := rfl
  rw [hsc, abs_le]
  constructor <;> nlinarith [hle]
