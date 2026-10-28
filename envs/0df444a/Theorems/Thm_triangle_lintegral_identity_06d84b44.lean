-- Prove2me | Theorems.Thm_triangle_lintegral_identity_06d84b44
-- name    : triangle_lintegral_identity_06d84b44
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T13:02:55.602685+00:00
-- url     : https://prove2.me/theorems/1c75e718-78b5-4bbc-ba31-69f4e625b1ea
-- title:
--   Time-triangle integral equals its indicator-kernel iterated integral
-- statement:
--   Given a measurable nonnegative extended-real function h, define S={(s,t):0<s<t} and F(s,t)=1_S(s,t) h(s,t-s). Assuming S and F measurable, integration of h(s,t-s) over the positive time triangle equals the unrestricted iterated integral of F(s,t). The proof expands the two indicators. This is a mechanically extracted helper from Scott Armstrong's MarkovProcess library, licensed Apache 2.0.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Analysis/ExpPrimitive.lean#L45-L69

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
theorem triangle_lintegral_identity_06d84b44 {h : ℝ × ℝ → ℝ≥0∞} (hh : Measurable h) 
    (hS : (let S : Set (ℝ × ℝ) := {p | 0 < p.1 ∧ p.1 < p.2}; let F : ℝ × ℝ → ℝ≥0∞ := fun p ↦ S.indicator (fun z ↦ h (z.1, z.2 - z.1)) p; MeasurableSet S))
    (hF : (let S : Set (ℝ × ℝ) := {p | 0 < p.1 ∧ p.1 < p.2}; let F : ℝ × ℝ → ℝ≥0∞ := fun p ↦ S.indicator (fun z ↦ h (z.1, z.2 - z.1)) p; Measurable F))
    : (let S : Set (ℝ × ℝ) := {p | 0 < p.1 ∧ p.1 < p.2}; let F : ℝ × ℝ → ℝ≥0∞ := fun p ↦ S.indicator (fun z ↦ h (z.1, z.2 - z.1)) p; (∫⁻ t in Ioi (0 : ℝ), ∫⁻ s in Ioo (0 : ℝ) t, h (s, t - s)) =
      ∫⁻ t, ∫⁻ s, F (s, t)) := by sorry
end
