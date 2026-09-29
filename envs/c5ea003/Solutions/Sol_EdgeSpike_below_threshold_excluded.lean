-- Prove2me | solution 1 for EdgeSpike.below_threshold_excluded
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T02:47:23.01565+00:00
-- url     : https://prove2.me/submissions/13637e33-6ed1-4143-86d0-5e4903fc25c7

-- Sol generated from MachineLearning/EdgeSpikeCensoring.lean
import Mathlib
import Definitions.Def_MachineLearning_EdgeSpikeCensoring
import Theorems.Thm_EdgeSpike_hasDerivAt_truncExpCDF

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






/-- Strict convexity of `exp` on `[0, b]`: the chord inequality that drives the
monotonicity of the censored edge mass. -/
lemma exp_mul_lt (b t : ℝ) (hb : 0 < b) (ht0 : 0 < t) (ht1 : t < 1) :
    exp (b * t) - 1 < t * (exp b - 1) := by
  have hne : b ≠ (0 : ℝ) := ne_of_gt hb
  have h := strictConvexOn_exp.2 (Set.mem_univ b) (Set.mem_univ (0 : ℝ)) hne ht0
    (show (0 : ℝ) < 1 - t by linarith) (show t + (1 - t) = 1 by ring)
  simp only [smul_eq_mul, mul_zero, add_zero, Real.exp_zero, mul_one] at h
  rw [mul_comm b t]
  nlinarith [h]



variable {t : ℝ}


/-- The numerator of `d/db (truncExpCDF b t)` is positive: this is exactly the
strict convexity inequality `exp (b t) - 1 < t (exp b - 1)`. -/
lemma truncExpCDF_deriv_num_pos (b t : ℝ) (hb : 0 < b) (ht0 : 0 < t) (ht1 : t < 1) :
    0 < t * exp (-(b * t)) * (1 - exp (-b)) - (1 - exp (-(b * t))) * exp (-b) := by
  have hconv := exp_mul_lt b t hb ht0 ht1
  have hA : (0 : ℝ) < exp (b * t) := Real.exp_pos _
  have hB : (0 : ℝ) < exp b := Real.exp_pos _
  have e1 : exp (-(b * t)) = (exp (b * t))⁻¹ := by rw [Real.exp_neg]
  have e2 : exp (-b) = (exp b)⁻¹ := by rw [Real.exp_neg]
  rw [e1, e2]
  rw [show t * (exp (b * t))⁻¹ * (1 - (exp b)⁻¹) - (1 - (exp (b * t))⁻¹) * (exp b)⁻¹ =
      (t * (exp b - 1) - (exp (b * t) - 1)) / (exp (b * t) * exp b) by
    field_simp]
  exact div_pos (by linarith) (mul_pos hA hB)

lemma truncExpCDF_deriv_pos (b t : ℝ) (hb : 0 < b) (ht0 : 0 < t) (ht1 : t < 1) :
    0 < deriv (fun x => truncExpCDF x t) b := by
  rw [(hasDerivAt_truncExpCDF b t hb).deriv]
  have hden : (0 : ℝ) < (1 - exp (-b)) ^ 2 := by
    have := one_sub_exp_neg_pos hb; positivity
  exact div_pos (truncExpCDF_deriv_num_pos b t hb ht0 ht1) hden

/-- **The censored edge mass is strictly increasing in the steepness.** -/
theorem truncExpCDF_strictMonoOn (ht0 : 0 < t) (ht1 : t < 1) :
    StrictMonoOn (fun x => truncExpCDF x t) (Set.Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
  · intro x hx
    exact ((hasDerivAt_truncExpCDF x t hx).continuousAt).continuousWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    exact truncExpCDF_deriv_pos x t hx ht0 ht1



variable {b t : ℝ}





variable {h p q rho t b : ℝ}




lemma edgeProb_strictMonoOn (hrho : 0 < rho) (ht0 : 0 < t) (ht1 : t < 1) :
    StrictMonoOn (fun b => edgeProb rho t b) (Set.Ioi 0) := by
  intro x hx y hy hxy
  have hmono : truncExpCDF x t < truncExpCDF y t :=
    truncExpCDF_strictMonoOn ht0 ht1 hx hy hxy
  show edgeProb rho t x < edgeProb rho t y
  unfold edgeProb
  nlinarith






variable {rho t : ℝ}







open EdgeSpike in
theorem solution(hrho0 : 0 < rho) (ht0 : 0 < t) (ht1 : t < 1)
    {v eps b b₁ : ℝ} (heps : 0 ≤ eps) (hb : 0 < b) (hbb : b ≤ b₁)
    (hexcl : edgeProb rho t b₁ + eps < v) :
    eps < |edgeProb rho t b - v| := by
  have hb1 : 0 < b₁ := lt_of_lt_of_le hb hbb
  have hmono : edgeProb rho t b ≤ edgeProb rho t b₁ := by
    rcases eq_or_lt_of_le hbb with h | h
    · rw [h]
    · exact (edgeProb_strictMonoOn hrho0 ht0 ht1 (Set.mem_Ioi.mpr hb)
        (Set.mem_Ioi.mpr hb1) h).le
  have hlt : edgeProb rho t b + eps < v := by linarith
  have : eps < v - edgeProb rho t b := by linarith
  calc eps < v - edgeProb rho t b := this
    _ = |edgeProb rho t b - v| := by
        rw [abs_sub_comm, abs_of_pos (by linarith)]
