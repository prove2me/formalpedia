-- Prove2me | solution 1 for EdgeSpike.truncExpCDF_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T02:48:30.710199+00:00
-- url     : https://prove2.me/submissions/f6169984-193e-40a2-8509-d9703ee9881a

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



lemma truncExpCDF_le_one (hb : 0 < b) (ht1 : t ≤ 1) : truncExpCDF b t ≤ 1 := by
  have hden := one_sub_exp_neg_pos hb
  have hlt : exp (-b) ≤ exp (-(b * t)) := by
    apply Real.exp_le_exp.mpr; nlinarith
  unfold truncExpCDF
  rw [div_le_one hden]
  linarith






variable {t : ℝ}







variable {b t : ℝ}





variable {h p q rho t b : ℝ}










variable {rho t : ℝ}







open EdgeSpike in
theorem solution(ht0 : 0 < t) (ht1 : t ≤ 1) :
    Tendsto (fun b => truncExpCDF b t) atTop (𝓝 1) := by
  have hrhs : Tendsto (fun b : ℝ => 2 * exp (-(b * t))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun b : ℝ => -(b * t)) atTop atBot := by
      have h2 : Tendsto (fun b : ℝ => b * t) atTop atTop :=
        Filter.Tendsto.atTop_mul_const ht0 tendsto_id
      exact tendsto_neg_atTop_atBot.comp h2
    simpa using (Real.tendsto_exp_atBot.comp h1).const_mul 2
  have hsq : Tendsto (fun b : ℝ => 1 - truncExpCDF b t) atTop (𝓝 0) := by
    apply squeeze_zero' (g := fun b : ℝ => 2 * exp (-(b * t)))
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with b hb
      have hb0 : (0 : ℝ) < b := lt_of_lt_of_le zero_lt_one hb
      have := truncExpCDF_le_one hb0 ht1
      linarith
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with b hb
      exact one_sub_truncExpCDF_le hb ht1
    · exact hrhs
  have hfin := hsq.const_sub (1 : ℝ)
  simpa using hfin
