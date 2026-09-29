-- Prove2me | solution 1 for GrokkingTraining.crossTime_diverges_at_criticality
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T20:52:44.615742+00:00
-- url     : https://prove2.me/submissions/77729283-3466-4f1f-80af-b33d4ffb8157

-- Sol generated from MachineLearning/GrokkingDelayedTransition/GradientFlowThreshold.lean
import Mathlib
import Definitions.Def_MachineLearning_GrokkingDelayedTransition_GradientFlowThreshold
import Theorems.Thm_GrokkingTraining_crossTime_lower_bound

/-!
# Deriving the grokking delay from weight-decayed training dynamics

In `Catalog/MachineLearning/GrokkingPhaseTransition.lean` the delay of the
two-layer ReLU network is *prescribed*: the bias is `-delay` by fiat.  This file
carries out Future Direction 2 (training dynamics) and part of Direction 6
(connection theorem): the delay is *derived* as the crossing time of a
weight-decayed gradient flow / gradient descent, and the bifurcation parameter of
the saddle-node normal form becomes an explicit function of the weight-decay
strength.

Main results.

* `wdFlow_hasDerivAt`, `wdFlow_isGradientFlow`, `wdFlow_init`: the explicit
  trajectory `w(t) = s/λ + (w₀ - s/λ) e^{-λ t}` is *the* gradient flow of the
  weight-decayed loss `λ w²/2 - s w`.
* `wdFlow_strictMono`, `wdFlow_lt_limit`: the trained weight increases strictly
  towards, but never reaches, the regularized optimum `s/λ`.
* `wdFlow_gt_threshold_iff`: the trajectory exceeds a fixed activation threshold
  `θ` *exactly* after the explicit time `crossTime = λ⁻¹ log((s/λ-w₀)/(s/λ-θ))`.
* `trained_relu_delayed_transition`: consequently the trained ReLU unit outputs
  exactly `0` up to `crossTime` and is strictly positive afterwards — the
  catalog's delayed transition, now with a *derived* delay.
* `crossing_exists_iff_subcritical_decay`: the threshold is crossed at all iff
  the weight decay is subcritical, `λ < λ_c := s/θ`, i.e. iff the saddle-node
  parameter `bifParam := s/λ - θ` is positive.  This is the promised connection
  between the optimization/regularization parameter and the normal form.
* `crossTime_diverges_at_criticality`: the delay is unbounded as the weight decay
  approaches its critical value — the grokking time diverges at the bifurcation.
* `gdSeq_closed_form`, `gd_delay_lower_bound`: the discrete weight-decayed
  gradient-descent iteration has the analogous closed form, and the number of
  steps before the threshold is crossed grows like `log(1/gap)`.
-/

open GrokkingTraining

open Real

/-! ### The weight-decayed loss and its gradient flow -/







/-! ### Monotone approach to the regularized optimum -/


/-! ### The crossing time: an explicit, derived delay -/





/-! ### The weight decay as bifurcation parameter -/





/-! ### Divergence of the delay at criticality -/



/-! ### Discrete weight-decayed gradient descent -/





open GrokkingTraining in
theorem solution(s theta w0 : ℝ) (hth : 0 < theta)
    (hw0 : w0 < theta) (hs : 0 < s) (T : ℝ) :
    ∃ lam : ℝ, 0 < lam ∧ lam < criticalDecay s theta ∧
      T < crossTime lam s w0 theta := by
  have hgap : 0 < theta - w0 := by linarith
  set c : ℝ := criticalDecay s theta with hc
  have hcpos : 0 < c := by simp only [hc, criticalDecay]; positivity
  obtain ⟨mu, hmupos, hmusmall, hmuhalf⟩ :
      ∃ mu : ℝ, 0 < mu ∧ mu < (theta - w0) * Real.exp (-(c * T)) ∧
        mu ≤ (theta - w0) / 2 := by
    refine ⟨min ((theta - w0) * Real.exp (-(c * T)) / 2) ((theta - w0) / 2), ?_, ?_, ?_⟩
    · exact lt_min (by positivity) (by positivity)
    · have h1 : 0 < (theta - w0) * Real.exp (-(c * T)) := by positivity
      exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
    · exact min_le_right _ _
  refine ⟨s / (theta + mu), by positivity, ?_, ?_⟩
  · simp only [hc, criticalDecay]
    exact div_lt_div_of_pos_left hs hth (by linarith)
  · set lam : ℝ := s / (theta + mu) with hlamdef
    have hlampos : 0 < lam := by positivity
    have hquot : s / lam = theta + mu := by
      simp only [hlamdef]; field_simp
    have hthlt : theta < s / lam := by rw [hquot]; linarith
    have hlb := crossTime_lower_bound lam s w0 theta hlampos hw0 hthlt
    have hbif : bifParam lam s theta = mu := by simp only [bifParam, hquot]; ring
    rw [hbif] at hlb
    have hlamle : lam ≤ c := by
      simp only [hlamdef, hc, criticalDecay]
      exact div_le_div_of_nonneg_left hs.le hth (by linarith)
    have hratio : 1 ≤ (theta - w0) / mu := by
      rw [le_div_iff₀ hmupos]; linarith
    have hlogpos : 0 ≤ Real.log ((theta - w0) / mu) := Real.log_nonneg hratio
    have hlog : c * T < Real.log ((theta - w0) / mu) := by
      have hlt : Real.exp (c * T) < (theta - w0) / mu := by
        rw [lt_div_iff₀ hmupos]
        have hexp : Real.exp (c * T) * Real.exp (-(c * T)) = 1 := by
          rw [← Real.exp_add]; simp
        nlinarith [Real.exp_pos (c * T)]
      have hh := Real.log_lt_log (Real.exp_pos (c * T)) hlt
      rwa [Real.log_exp] at hh
    have hTlt : T < (1 / c) * Real.log ((theta - w0) / mu) := by
      have hmul := mul_lt_mul_of_pos_left hlog (show (0 : ℝ) < 1 / c by positivity)
      have hid : (1 / c) * (c * T) = T := by field_simp
      linarith [hmul, hid.le, hid.ge]
    have hcompare : (1 / c) * Real.log ((theta - w0) / mu)
        ≤ (1 / lam) * Real.log ((theta - w0) / mu) :=
      mul_le_mul_of_nonneg_right (one_div_le_one_div_of_le hlampos hlamle) hlogpos
    linarith
