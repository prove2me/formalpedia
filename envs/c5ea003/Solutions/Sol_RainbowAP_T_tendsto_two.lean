-- Prove2me | solution 1 for RainbowAP.T_tendsto_two
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T01:31:10.50896+00:00
-- url     : https://prove2.me/submissions/01f6384b-a4d0-4424-9f65-c7a593264551

-- Sol generated from Shared/RainbowAPPairThreshold.lean
import Mathlib
import Definitions.Def_Shared_RainbowAPPairThreshold
import Theorems.Thm_RainbowAP_T_lower_bound
import Theorems.Thm_RainbowAP_T_upper_bound

/-!
# The rainbow pair-spectrum threshold `T_k` and its exact `Θ(k² log k)` growth

Fix a palette of `k` colours.  A colouring of a block-decomposed interval realises the
*full pair spectrum* if every one of the `k²` ordered colour pairs `(i, j)` occurs on some
2-term arithmetic progression of the decomposition.  `T k` is the least number of blocks at
which a strict majority of colourings has full pair spectrum; formally it is the full-spectrum
threshold of the alphabet `Fin k × Fin k`.

Main results.

* `RainbowAP.T_lower_bound` : `2 k² log k - 2 log k ≤ T k`.
* `RainbowAP.T_upper_bound` : `T k ≤ 2 k² log k + k² log 2 + 1`.
* `RainbowAP.T_theta`       : explicit constants `c₁ = 1`, `c₂ = 4` with
  `0.1 ≤ c₁ ≤ c₂ ≤ 10` sandwiching `T k` between `c₁ k² log k` and `c₂ k² log k` for `k ≥ 2`.
* `RainbowAP.T_tendsto_two` : `T k / (k² log k) → 2`, so the optimal constants coincide,
  `c₁ = c₂ = 2`.
* `RainbowAP.T_liminf`, `RainbowAP.T_limsup` : the `lim inf` and the `lim sup` both equal `2`.
-/

open Finset Real Filter Topology

open RainbowAP











open RainbowAP in
theorem solution:
    Tendsto (fun k : ℕ => (T k : ℝ) / ((k : ℝ) ^ 2 * Real.log k)) atTop (𝓝 2) := by
  have hnat : Tendsto (fun k : ℕ => (k : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hsq : Tendsto (fun k : ℕ => (k : ℝ) ^ 2) atTop atTop := by
    have := hnat.atTop_mul_atTop₀ hnat
    simpa [sq] using this
  have hlog : Tendsto (fun k : ℕ => Real.log k) atTop atTop :=
    Real.tendsto_log_atTop.comp hnat
  have hprod : Tendsto (fun k : ℕ => (k : ℝ) ^ 2 * Real.log k) atTop atTop :=
    hsq.atTop_mul_atTop₀ hlog
  have hinvsq : Tendsto (fun k : ℕ => 2 / (k : ℝ) ^ 2) atTop (𝓝 0) := by
    simpa using hsq.const_div_atTop (2 : ℝ)
  have hinvlog : Tendsto (fun k : ℕ => Real.log 2 / Real.log k) atTop (𝓝 0) := by
    simpa using hlog.const_div_atTop (Real.log 2)
  have hinvprod : Tendsto (fun k : ℕ => 1 / ((k : ℝ) ^ 2 * Real.log k)) atTop (𝓝 0) := by
    simpa using hprod.const_div_atTop (1 : ℝ)
  have hlow : Tendsto (fun k : ℕ => 2 - 2 / (k : ℝ) ^ 2) atTop (𝓝 2) := by
    have := (tendsto_const_nhds (x := (2 : ℝ)) (f := atTop (α := ℕ))).sub hinvsq
    simpa using this
  have hupp : Tendsto
      (fun k : ℕ => 2 + Real.log 2 / Real.log k + 1 / ((k : ℝ) ^ 2 * Real.log k))
      atTop (𝓝 2) := by
    have h1 := (tendsto_const_nhds (x := (2 : ℝ)) (f := atTop (α := ℕ))).add hinvlog
    have h2 := h1.add hinvprod
    simpa using h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hupp ?_ ?_
  · filter_upwards [eventually_ge_atTop 2] with k hk
    have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hlogk : (0 : ℝ) < Real.log k := Real.log_pos (by linarith)
    have hD : (0 : ℝ) < (k : ℝ) ^ 2 * Real.log k := by positivity
    rw [le_div_iff₀ hD]
    have hlow := T_lower_bound k hk
    have hsq2 : (0 : ℝ) < (k : ℝ) ^ 2 := by positivity
    have hexp : (2 - 2 / (k : ℝ) ^ 2) * ((k : ℝ) ^ 2 * Real.log k)
        = 2 * (k : ℝ) ^ 2 * Real.log k - 2 * Real.log k := by
      field_simp
    rw [hexp]
    exact hlow
  · filter_upwards [eventually_ge_atTop 2] with k hk
    have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hlogk : (0 : ℝ) < Real.log k := Real.log_pos (by linarith)
    have hD : (0 : ℝ) < (k : ℝ) ^ 2 * Real.log k := by positivity
    rw [div_le_iff₀ hD]
    have hup := T_upper_bound k hk
    have hexp : (2 + Real.log 2 / Real.log k + 1 / ((k : ℝ) ^ 2 * Real.log k))
        * ((k : ℝ) ^ 2 * Real.log k)
        = 2 * (k : ℝ) ^ 2 * Real.log k + (k : ℝ) ^ 2 * Real.log 2 + 1 := by
      field_simp
    rw [hexp]
    exact hup
