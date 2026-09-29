-- Prove2me | solution 1 for ChebotarevGeodesic.sparseCount_no_short_window
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T21:03:37.312591+00:00
-- url     : https://prove2.me/submissions/ff5c38c6-c8fa-42b4-bd20-1f9d3483a382

-- Sol generated from Shared/ChebotarevGeodesicGaps.lean
import Mathlib
import Definitions.Def_Shared_ChebotarevGeodesic
import Definitions.Def_Shared_ChebotarevGeodesicGaps
import Definitions.Def_Shared_ChebotarevGeodesicTorus
import Theorems.Thm_ChebotarevGeodesic_eventually_rpow_lt_rpow
import Theorems.Thm_ChebotarevGeodesic_rpow_bernoulli_add_le
import Theorems.Thm_ChebotarevGeodesic_sparseCount_eq_of_mem_Ico
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
theorem solution{δ γ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hγ : γ < 1 - δ)
    (B : ℝ) :
    ∃ x, B ≤ x ∧ 1 ≤ x ∧ sparseCount δ (x + x ^ γ) = sparseCount δ x := by
  set p : ℝ := 1 / δ with hpdef
  have hp0 : 0 < p := by positivity
  have hp : 1 ≤ p := by rw [hpdef, le_div_iff₀ hδ0]; linarith
  have hpe : p * (1 - δ) = p - 1 := by rw [hpdef]; field_simp
  have hdom : ∀ᶠ z : ℝ in atTop, 1 * z ^ γ < p * z ^ (1 - δ) :=
    eventually_rpow_lt_rpow hγ one_pos hp0
  obtain ⟨N, hN⟩ := eventually_atTop.mp hdom
  set m : ℕ := max (max ⌈N⌉₊ ⌈B⌉₊) 1 with hmdef
  have hm1 : 1 ≤ m := le_max_right _ _
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
  have hm1' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
  have hmN : N ≤ (m : ℝ) :=
    le_trans (Nat.le_ceil N) (by exact_mod_cast le_trans (le_max_left _ _) (le_max_left _ _))
  have hmB : B ≤ (m : ℝ) :=
    le_trans (Nat.le_ceil B) (by exact_mod_cast le_trans (le_max_right _ _) (le_max_left _ _))
  set x : ℝ := (m : ℝ) ^ p with hxdef
  have hxm : (m : ℝ) ≤ x := by
    calc (m : ℝ) = (m : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (m : ℝ) ^ p := Real.rpow_le_rpow_of_exponent_le hm1' hp
  have hx1 : (1 : ℝ) ≤ x := le_trans hm1' hxm
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx1
  have hxγ : (0 : ℝ) < x ^ γ := Real.rpow_pos_of_pos hx0 _
  have hbern := rpow_bernoulli_add_le hm0 zero_le_one hp
  rw [mul_one] at hbern
  have hmx : (m : ℝ) ^ (p - 1) = x ^ (1 - δ) := by rw [hxdef, ← Real.rpow_mul hm0.le, hpe]
  rw [hmx] at hbern
  have hgap := hN x (le_trans hmN hxm)
  rw [one_mul] at hgap
  have hnext : x + p * x ^ (1 - δ) ≤ ((m : ℝ) + 1) ^ p := by rw [hxdef]; linarith [hbern]
  have hupper : x + x ^ γ < ((m : ℝ) + 1) ^ p := by linarith
  refine ⟨x, le_trans hmB hxm, hx1, ?_⟩
  rw [sparseCount_eq_of_mem_Ico hδ0 hm1 (by rw [hxdef]; linarith) hupper,
    sparseCount_eq_of_mem_Ico hδ0 hm1 (le_of_eq hxdef.symm) (by
      have hppos : (0 : ℝ) < p * x ^ (1 - δ) := by positivity
      linarith)]
