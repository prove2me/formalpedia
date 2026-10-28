-- Prove2me | Theorems.Thm_triangle_lintegral_identity_b176d7f6
-- name    : triangle_lintegral_identity_b176d7f6
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T13:02:56.569106+00:00
-- url     : https://prove2.me/theorems/305eef0d-3cab-4179-b5d6-317a46cd034a
-- title:
--   Positive quadrant integral equals the sheared indicator-kernel integral
-- statement:
--   With S={(s,t):0<s<t} and F(s,t)=1_S(s,t) h(s,t-s), integration of h(s,u) over s>0,u>0 equals integration of F(s,s+u). The hypotheses include the measurability of S and F and an additional available left-hand identity. The proof compares the indicator functions pointwise. This is a mechanically extracted helper from Scott Armstrong's MarkovProcess library, licensed Apache 2.0.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Analysis/ExpPrimitive.lean#L70-L98

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Prod
open MeasureTheory Set
open scoped ENNReal
open intervalIntegral

noncomputable section
theorem triangle_lintegral_identity_b176d7f6 {h : ℝ × ℝ → ℝ≥0∞} (hh : Measurable h) 
    (hS : (let S : Set (ℝ × ℝ) := {p | 0 < p.1 ∧ p.1 < p.2}; let F : ℝ × ℝ → ℝ≥0∞ := fun p ↦ S.indicator (fun z ↦ h (z.1, z.2 - z.1)) p; MeasurableSet S))
    (hF : (let S : Set (ℝ × ℝ) := {p | 0 < p.1 ∧ p.1 < p.2}; let F : ℝ × ℝ → ℝ≥0∞ := fun p ↦ S.indicator (fun z ↦ h (z.1, z.2 - z.1)) p; Measurable F))
    (hleft : (let S : Set (ℝ × ℝ) := {p | 0 < p.1 ∧ p.1 < p.2}; let F : ℝ × ℝ → ℝ≥0∞ := fun p ↦ S.indicator (fun z ↦ h (z.1, z.2 - z.1)) p; (∫⁻ t in Ioi (0 : ℝ), ∫⁻ s in Ioo (0 : ℝ) t, h (s, t - s)) =
      ∫⁻ t, ∫⁻ s, F (s, t)))
    : (let S : Set (ℝ × ℝ) := {p | 0 < p.1 ∧ p.1 < p.2}; let F : ℝ × ℝ → ℝ≥0∞ := fun p ↦ S.indicator (fun z ↦ h (z.1, z.2 - z.1)) p; (∫⁻ s in Ioi (0 : ℝ), ∫⁻ u in Ioi (0 : ℝ), h (s, u)) =
      ∫⁻ s, ∫⁻ u, F (s, s + u)) := by sorry
end
