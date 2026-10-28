-- Prove2me | Theorems.Thm_intervalIntegral_lintegral_timeTriangle_sub
-- name    : intervalIntegral.lintegral_timeTriangle_sub
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T12:53:56.499922+00:00
-- url     : https://prove2.me/theorems/c7f3e7a4-3e37-48d6-b739-b9c477f1d19d
-- title:
--   Tonelli identity for a positive time triangle under a shear
-- statement:
--   For a measurable function h from pairs of real numbers to nonnegative extended reals, the iterated integral over 0 < s < t of h(s,t-s), for t > 0, equals the iterated integral over s > 0 and u > 0 of h(s,u). The proof applies Tonelli's theorem and the measure-preserving shear (s,u) ↦ (s,s+u). Source: Scott Armstrong, MarkovProcess (Apache-2.0); original commit and line range retained.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Analysis/ExpPrimitive.lean#L35-L111

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

theorem intervalIntegral.lintegral_timeTriangle_sub {h : ℝ × ℝ → ℝ≥0∞} (hh : Measurable h) :
    (∫⁻ t in Ioi (0 : ℝ), ∫⁻ s in Ioo (0 : ℝ) t, h (s, t - s)) =
      ∫⁻ s in Ioi (0 : ℝ), ∫⁻ u in Ioi (0 : ℝ), h (s, u) := by sorry
