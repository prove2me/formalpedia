-- Prove2me | solution 1 for EdgeSpike.hasDerivAt_truncExpCDF
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T02:46:00.847027+00:00
-- url     : https://prove2.me/submissions/38e19721-6c46-4b4a-b89b-e15582806d63

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
theorem solution(b t : ℝ) (hb : 0 < b) :
    HasDerivAt (fun x => truncExpCDF x t)
      ((t * exp (-(b * t)) * (1 - exp (-b)) - (1 - exp (-(b * t))) * exp (-b)) /
        (1 - exp (-b)) ^ 2) b := by
  have hden : (1 : ℝ) - exp (-b) ≠ 0 := ne_of_gt (one_sub_exp_neg_pos hb)
  have hnum : HasDerivAt (fun x : ℝ => 1 - exp (-(x * t))) (t * exp (-(b * t))) b := by
    have h1 : HasDerivAt (fun x : ℝ => -(x * t)) (-t) b := by
      simpa using ((hasDerivAt_id b).mul_const t).neg
    have h2 := h1.exp
    have h3 := h2.const_sub (1 : ℝ)
    convert h3 using 1
    ring
  have hd : HasDerivAt (fun x : ℝ => 1 - exp (-x)) (exp (-b)) b := by
    have h1 : HasDerivAt (fun x : ℝ => -x) (-1 : ℝ) b := by simpa using (hasDerivAt_id b).neg
    have h2 := h1.exp
    have h3 := h2.const_sub (1 : ℝ)
    convert h3 using 1
    ring
  exact hnum.div hd hden
