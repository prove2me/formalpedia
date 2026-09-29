-- Prove2me | solution 1 for EdgeSpike.identified_ray
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T02:48:30.133468+00:00
-- url     : https://prove2.me/submissions/7bfa7eb5-a03e-416e-b526-9fecbe93fb97

-- Sol generated from MachineLearning/EdgeSpikeCensoring.lean
import Mathlib
import Definitions.Def_MachineLearning_EdgeSpikeCensoring
import Theorems.Thm_EdgeSpike_one_sub_truncExpCDF_le

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

lemma one_sub_exp_neg_pos (hb : 0 < b) : 0 < 1 - exp (-b) := by
  have : exp (-b) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  linarith


lemma truncExpCDF_lt_one (hb : 0 < b) (ht1 : t < 1) :
    truncExpCDF b t < 1 := by
  have hden := one_sub_exp_neg_pos hb
  have hlt : exp (-b) < exp (-(b * t)) := by
    apply Real.exp_lt_exp.mpr; nlinarith
  unfold truncExpCDF
  rw [div_lt_one hden]
  linarith







variable {t : ℝ}







variable {b t : ℝ}





variable {h p q rho t b : ℝ}


lemma edgeProb_lt_limit (hrho : 0 < rho) (hb : 0 < b) (ht1 : t < 1) :
    edgeProb rho t b < edgeProbLimit rho t := by
  unfold edgeProb edgeProbLimit
  have := truncExpCDF_lt_one hb ht1
  nlinarith








variable {rho t : ℝ}







open EdgeSpike in
theorem solution(hrho0 : 0 < rho) (hrho1 : rho < 1) (ht0 : 0 < t) (ht1 : t < 1)
    {v eps B₀ b : ℝ} (hv1 : edgeProbLimit rho t - eps ≤ v)
    (hv2 : v ≤ edgeProbLimit rho t) (hB0 : 1 ≤ B₀)
    (hB0' : 2 * rho * exp (-(B₀ * t)) ≤ eps) (hb : B₀ ≤ b) :
    |edgeProb rho t b - v| ≤ eps := by
  have hb1 : (1 : ℝ) ≤ b := le_trans hB0 hb
  have hb0 : (0 : ℝ) < b := lt_of_lt_of_le zero_lt_one hb1
  have hple : edgeProb rho t b < edgeProbLimit rho t := edgeProb_lt_limit hrho0 hb0 ht1
  have hcen := one_sub_truncExpCDF_le hb1 ht1.le
  have hgap : edgeProbLimit rho t - edgeProb rho t b ≤ 2 * rho * exp (-(b * t)) := by
    unfold edgeProb edgeProbLimit
    nlinarith
  have hmono : exp (-(b * t)) ≤ exp (-(B₀ * t)) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hsmall : edgeProbLimit rho t - edgeProb rho t b ≤ eps := by
    have : 2 * rho * exp (-(b * t)) ≤ 2 * rho * exp (-(B₀ * t)) := by nlinarith
    linarith
  rw [abs_le]
  constructor <;> linarith
