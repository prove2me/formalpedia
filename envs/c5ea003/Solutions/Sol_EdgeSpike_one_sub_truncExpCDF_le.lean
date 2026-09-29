-- Prove2me | solution 1 for EdgeSpike.one_sub_truncExpCDF_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T02:47:24.417623+00:00
-- url     : https://prove2.me/submissions/ef6c89fe-efde-4f25-9af2-e03520e93f7f

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

lemma one_sub_exp_neg_pos (hb : 0 < b) : 0 < 1 - exp (-b) := by
  have : exp (-b) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  linarith









variable {t : ℝ}







variable {b t : ℝ}





variable {h p q rho t b : ℝ}










variable {rho t : ℝ}







open EdgeSpike in
theorem solution(hb : 1 ≤ b) (ht1 : t ≤ 1) :
    1 - truncExpCDF b t ≤ 2 * exp (-(b * t)) := by
  have hb0 : (0 : ℝ) < b := lt_of_lt_of_le zero_lt_one hb
  have hden := one_sub_exp_neg_pos hb0
  have hhalf : (1 : ℝ) / 2 ≤ 1 - exp (-b) := by
    have h1 : exp (-b) ≤ exp (-1 : ℝ) := Real.exp_le_exp.mpr (by linarith)
    have h2 : exp (-1 : ℝ) < 1 / 2 := by
      rw [Real.exp_neg]
      have he : (2 : ℝ) < exp 1 := by
        have := Real.exp_one_gt_d9
        linarith
      rw [inv_lt_comm₀ (Real.exp_pos _) (by norm_num)]
      linarith
    linarith
  have key : 1 - truncExpCDF b t = (exp (-(b * t)) - exp (-b)) / (1 - exp (-b)) := by
    unfold truncExpCDF
    field_simp
    ring
  rw [key, div_le_iff₀ hden]
  have hnn : 0 ≤ exp (-(b * t)) - exp (-b) := by
    have : exp (-b) ≤ exp (-(b * t)) := Real.exp_le_exp.mpr (by nlinarith)
    linarith
  nlinarith [Real.exp_pos (-(b * t)), Real.exp_pos (-b)]
