-- Prove2me | solution 1 for ChebotarevGeodesic.eventually_lt_of_additive_window
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T20:50:39.35639+00:00
-- url     : https://prove2.me/submissions/a7f69f84-fd36-456c-9614-6f977fc4dff6

-- Sol generated from Shared/ChebotarevGeodesicGaps.lean
import Mathlib
import Definitions.Def_Shared_ChebotarevGeodesic
import Definitions.Def_Shared_ChebotarevGeodesicGaps
import Definitions.Def_Shared_ChebotarevGeodesicTorus
import Theorems.Thm_ChebotarevGeodesic_eventually_rpow_lt_rpow
import Theorems.Thm_ChebotarevGeodesic_rpow_bernoulli_add_le
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
theorem solution{pi : ℝ → ℝ} {θ β c γ : ℝ}
    (h : HasErrorExponent pi (fun x => c * x ^ β) θ) (hc : 0 < c) (hβ : 1 ≤ β) (hθ : 0 ≤ θ)
    (hγ1 : γ ≤ 1) (hγ : 1 - (β - θ) < γ) :
    ∀ᶠ x in atTop, pi x < pi (x + x ^ γ) := by
  set gap : ℝ := γ - 1 + β - θ with hgapdef
  have hgap : 0 < gap := by simp only [hgapdef]; linarith
  set ε : ℝ := gap / 2 with hεdef
  have hε : 0 < ε := by positivity
  set θ' : ℝ := θ + ε with hθ'def
  have hθ'0 : 0 ≤ θ' := by simp only [hθ'def]; linarith
  have hlt : θ' < β - 1 + γ := by simp only [hθ'def, hεdef, hgapdef]; linarith
  obtain ⟨C, hC, X, hX, hb⟩ := h ε hε
  set t : ℝ := (2 : ℝ) ^ θ' with htdef
  have ht : 0 < t := Real.rpow_pos_of_pos (by norm_num) _
  have hdom := eventually_rpow_lt_rpow (a := θ') (b := β - 1 + γ)
    (K := C * t + C) (L := c * β) hlt (by positivity) (by nlinarith)
  filter_upwards [hdom, eventually_ge_atTop X, eventually_ge_atTop (1 : ℝ)] with x hx hxX hx1
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx1
  have hxγ : (0 : ℝ) < x ^ γ := Real.rpow_pos_of_pos hx0 _
  have hxγx : x ^ γ ≤ x := by
    calc x ^ γ ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 hγ1
      _ = x := Real.rpow_one x
  have hxX' : X ≤ x + x ^ γ := by linarith
  have h1 := hb x hxX
  have h2 := hb (x + x ^ γ) hxX'
  simp only [← hθ'def] at h1 h2
  have hA : x ^ (β - 1) * x ^ γ = x ^ (β - 1 + γ) := (Real.rpow_add hx0 _ _).symm
  have hbern := rpow_bernoulli_add_le hx0 hxγ.le hβ
  rw [mul_assoc, hA] at hbern
  have hQ : (x + x ^ γ) ^ θ' ≤ t * x ^ θ' := by
    have h2x : x + x ^ γ ≤ 2 * x := by linarith
    calc (x + x ^ γ) ^ θ' ≤ (2 * x) ^ θ' := Real.rpow_le_rpow (by positivity) h2x hθ'0
      _ = t * x ^ θ' := by rw [Real.mul_rpow (by norm_num) hx0.le]
  have hup : pi x ≤ c * x ^ β + C * x ^ θ' := by
    have := abs_le.mp h1; linarith [this.2]
  have hlow : c * (x + x ^ γ) ^ β - C * (x + x ^ γ) ^ θ' ≤ pi (x + x ^ γ) := by
    have := abs_le.mp h2; linarith [this.1]
  have step1 : c * (x ^ β + β * x ^ (β - 1 + γ)) ≤ c * (x + x ^ γ) ^ β :=
    mul_le_mul_of_nonneg_left hbern hc.le
  have step2 : C * (x + x ^ γ) ^ θ' ≤ C * (t * x ^ θ') :=
    mul_le_mul_of_nonneg_left hQ hC.le
  linarith
