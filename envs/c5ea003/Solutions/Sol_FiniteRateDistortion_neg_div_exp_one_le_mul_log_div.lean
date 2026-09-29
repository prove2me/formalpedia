-- Prove2me | solution 1 for FiniteRateDistortion.neg_div_exp_one_le_mul_log_div
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:39:37.418675+00:00
-- url     : https://prove2.me/submissions/8418510e-21cb-4ed2-a516-59ffb258005e

-- Sol generated from Bridges/FiniteRateDistortion/Core.lean
import Mathlib
import Definitions.Def_Bridges_FiniteRateDistortion_Core

/-!
# Finite rate–distortion theory: channels, mutual information, and the Lagrangian dual

This module supplies the objects used by
`Bridges/FiniteRateDistortion/TropicalEnvelope.lean`, which referred to a finite
rate-distortion vocabulary that no module in the catalog provided.

Everything is finite and elementary:

* `FinProbDist α`, `Channel α β` — a source distribution and a test channel;
* `mutualInfo`, `distortion` — the two functionals of a channel;
* `rateDistortion μ d D` — the infimum of the mutual information over channels meeting
  the distortion constraint;
* `lagrangianDual μ d s` — the infimum of `I(W) + s · d(W)`;
* `lagrangianDual_le_rateDistortion` — **weak duality**: `Φ(s) - s·D ≤ R(D)` for every
  slope `s ≥ 0`, the affine lower bound whose tropical envelope is studied downstream.

The only analytic input is the elementary estimate `w · log (w / q) ≥ -q/e`
(`neg_div_exp_one_le_mul_log_div`), which makes the Lagrangian set bounded below, so the
infima are genuine.
-/

open Finset

noncomputable section

open FiniteRateDistortion

variable {α β : Type*} [Fintype α] [Fintype β]

/-! ## Sources and channels -/







/-! ## The elementary entropy estimate -/

/-- `log u ≤ u / e`, the tangent bound at `u = e`. -/
theorem log_le_div_exp_one {u : ℝ} (hu : 0 < u) : Real.log u ≤ u / Real.exp 1 := by
  have h := Real.log_le_sub_one_of_pos (x := u / Real.exp 1) (by positivity)
  rw [Real.log_div hu.ne' (Real.exp_ne_zero 1), Real.log_exp] at h
  linarith


/-! ## Mutual information and distortion -/






/-! ## The rate–distortion function and its Lagrangian dual -/









open FiniteRateDistortion in
theorem solution{w q : ℝ} (hw : 0 ≤ w) (hq : 0 ≤ q) :
    -(q / Real.exp 1) ≤ w * Real.log (w / q) := by
  rcases eq_or_lt_of_le hw with hw0 | hw0
  · simp [← hw0]
    positivity
  rcases eq_or_lt_of_le hq with hq0 | hq0
  · simp [← hq0]
  · have h1 : Real.log (q / w) ≤ (q / w) / Real.exp 1 := log_le_div_exp_one (by positivity)
    have h2 : Real.log (q / w) = - Real.log (w / q) := by
      rw [← Real.log_inv]; congr 1; field_simp
    have h3 : -Real.log (w / q) ≤ (q / w) / Real.exp 1 := by rw [← h2]; exact h1
    have h4 : w * (-Real.log (w / q)) ≤ w * ((q / w) / Real.exp 1) :=
      mul_le_mul_of_nonneg_left h3 hw0.le
    have h5 : w * ((q / w) / Real.exp 1) = q / Real.exp 1 := by field_simp
    rw [h5] at h4
    linarith
