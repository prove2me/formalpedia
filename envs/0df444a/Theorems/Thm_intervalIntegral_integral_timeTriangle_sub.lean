-- Prove2me | Theorems.Thm_intervalIntegral_integral_timeTriangle_sub
-- name    : intervalIntegral.integral_timeTriangle_sub
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T18:09:10.848493+00:00
-- url     : https://prove2.me/theorems/4833bb26-2430-455e-9f91-b971f4ed6cd2
-- title:
--   Fubini integral of the positive time triangle under a measure-preserving shear
-- statement:
--   For an integrable measurable real-valued function on the positive quadrant, the integral over positive pairs with $0<s<t$ of $h(s,t-s)$ equals the positive-quadrant double integral of $h(s,u)$. This change of variables follows from the measure-preserving triangular shear and Fubini’s theorem.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Analysis/ExpPrimitive.lean#L115-L211

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

theorem intervalIntegral.integral_timeTriangle_sub {h : ℝ × ℝ → ℝ} (hh : Measurable h)
    (hint : Integrable ((Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)).indicator h)
      (volume.prod volume)) :
    (∫ t in Ioi (0 : ℝ), ∫ s in Ioo (0 : ℝ) t, h (s, t - s)) =
      ∫ s in Ioi (0 : ℝ), ∫ u in Ioi (0 : ℝ), h (s, u) := by sorry
