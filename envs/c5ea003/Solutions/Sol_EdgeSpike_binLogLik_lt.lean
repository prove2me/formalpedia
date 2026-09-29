-- Prove2me | solution 1 for EdgeSpike.binLogLik_lt
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T02:47:23.70214+00:00
-- url     : https://prove2.me/submissions/3c4bdff7-940f-439f-a533-227e655772cf

-- Sol generated from MachineLearning/EdgeSpikeCensoring.lean
import Mathlib
import Definitions.Def_MachineLearning_EdgeSpikeCensoring

/-!
# Edge-spike censoring: why the steepness of a left-edge spike is a lower bound only

## Motivation (exp 594 / paper 245, round-88 identifiability audit)

A pooled positional histogram was fitted with a two-component profile,
*flat bulk + left-edge spike*, where the spike is an exponential law with rate
`b` truncated to the unit interval.  Empirically the fitted `b_edge` "rode the
cap": it landed at `40.000` when the optimiser was capped at `40` and at `40.46`
when capped at `80`, with a bootstrap CI `[15.25, 80.0]` whose upper end is the
cap itself.  The registered analysis therefore had to be amended to
*"left-edge spike with `b_edge ≳ 15`, **lower bound only**"*.

This file proves that this behaviour is **not** an artefact of the optimiser:
it is a theorem about the model class.  Once the observable is the *mass in the
edge bin* `[0, t]`, the map `b ↦` (edge mass) is strictly increasing but
bounded, and it approaches its ceiling at rate `exp (-b t)`.  Consequently:

* `EdgeSpike.binLogLik_cap_riding` — the binned log-likelihood is **strictly
  increasing in `b`** whenever the empirical edge fraction is at least the
  ceiling `edgeProbLimit`.  Hence for every cap `B` the constrained optimum sits
  exactly at `b = B`: cap-riding is forced.
* `EdgeSpike.no_finite_maximiser` — no finite maximiser exists, so no cap raise
  produces an interior optimum.
* `EdgeSpike.cap_gain_le` — the total remaining log-likelihood available above a
  cap `B` is at most `C · exp (-B t)`.  Raising the cap buys exponentially
  little: at the audited geometry this is why `dAICc` moved only from `-101.28`
  to `-101.33` between caps `40` and `80`.

The three statements together are the formal content of the verdict
`H0_SPIKE_STEEPNESS_UNIDENTIFIABLE`: the data censor the steepness parameter.
-/

open EdgeSpike

open Real Filter Topology






variable {b t : ℝ}










variable {t : ℝ}







variable {b t : ℝ}





variable {h p q rho t b : ℝ}










variable {rho t : ℝ}







open EdgeSpike in
theorem solution(hh0 : 0 < h) (hh1 : h < 1) (hp : 0 < p) (hpq : p < q)
    (hqh : q ≤ h) : binLogLik h p < binLogLik h q := by
  have hq0 : 0 < q := lt_trans hp hpq
  have hq1 : q < 1 := lt_of_le_of_lt hqh hh1
  have hp1 : p < 1 := lt_trans hpq hq1
  have hq0' : q ≠ 0 := ne_of_gt hq0
  have hp0' : p ≠ 0 := ne_of_gt hp
  have hq1' : (1 : ℝ) - q ≠ 0 := by intro hc; linarith
  have hp1' : (1 : ℝ) - p ≠ 0 := by intro hc; linarith
  -- strict logarithmic lower bounds on both increments
  have hL : (q - p) / q < log q - log p := by
    have hx : (0 : ℝ) < p / q := div_pos hp hq0
    have hne : p / q ≠ 1 := by
      intro hc
      rw [div_eq_one_iff_eq hq0'] at hc
      linarith
    have hlog := Real.log_lt_sub_one_of_pos hx hne
    rw [Real.log_div hp0' hq0'] at hlog
    have hqq : p / q - 1 = -((q - p) / q) := by field_simp; ring
    rw [hqq] at hlog
    linarith
  have hM : -((q - p) / (1 - q)) < log (1 - q) - log (1 - p) := by
    have hx : (0 : ℝ) < (1 - p) / (1 - q) := div_pos (by linarith) (by linarith)
    have hne : (1 - p) / (1 - q) ≠ 1 := by
      intro hc
      rw [div_eq_one_iff_eq hq1'] at hc
      linarith
    have hlog := Real.log_lt_sub_one_of_pos hx hne
    rw [Real.log_div hp1' hq1'] at hlog
    have hqq : (1 - p) / (1 - q) - 1 = (q - p) / (1 - q) := by field_simp; ring
    rw [hqq] at hlog
    linarith
  -- the first-order terms already have the right sign, because `q ≤ h`
  have hcmp : (1 - h) * ((q - p) / (1 - q)) ≤ h * ((q - p) / q) := by
    rw [show (1 - h) * ((q - p) / (1 - q)) = ((1 - h) * (q - p)) / (1 - q) by ring,
      show h * ((q - p) / q) = (h * (q - p)) / q by ring,
      div_le_div_iff₀ (show (0 : ℝ) < 1 - q by linarith) hq0]
    nlinarith [mul_nonneg (sub_pos.mpr hpq).le (sub_nonneg.mpr hqh)]
  have hA : h * ((q - p) / q) < h * (log q - log p) := mul_lt_mul_of_pos_left hL hh0
  have hB : (1 - h) * (-((q - p) / (1 - q))) < (1 - h) * (log (1 - q) - log (1 - p)) :=
    mul_lt_mul_of_pos_left hM (by linarith)
  unfold binLogLik
  nlinarith [hA, hB, hcmp]
