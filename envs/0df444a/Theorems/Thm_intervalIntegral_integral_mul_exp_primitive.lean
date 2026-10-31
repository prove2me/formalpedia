-- Prove2me | Theorems.Thm_intervalIntegral_integral_mul_exp_primitive
-- name    : intervalIntegral.integral_mul_exp_primitive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:26:03.551843+00:00
-- url     : https://prove2.me/theorems/d66401ce-539f-47d8-b874-22aaada4feed
-- title:
--   MarkovProcess: integral_mul_exp_primitive
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Exponential of an integral primitive

This file proves the integral identity for the exponential of the primitive of a bounded
nonnegative integrable real function.  The proof compares the integral with left and right sums
on uniform partitions; in particular, it does not require pointwise differentiability of the
primitive.

Main results: `intervalIntegral.integral_mul_exp_primitive`,
`intervalIntegral.lintegral_timeTriangle_sub`, and `intervalIntegral.integral_timeTriangle_sub`.

No probabilistic structure is used or asserted.
-/

open MeasureTheory Set
open scoped ENNReal

namespace intervalIntegral

noncomputable section

-- The namespace placement is upstream-facing: this is a pure companion to interval integrals.










end

end intervalIntegral


open intervalIntegral
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Exponential of an integral primitive

This file proves the integral identity for the exponential of the primitive of a bounded
nonnegative integrable real function.  The proof compares the integral with left and right sums
on uniform partitions; in particular, it does not require pointwise differentiability of the
primitive.

Main results: `intervalIntegral.integral_mul_exp_primitive`,
`intervalIntegral.lintegral_timeTriangle_sub`, and `intervalIntegral.integral_timeTriangle_sub`.

No probabilistic structure is used or asserted.
-/

open MeasureTheory Set
open scoped ENNReal



-- The namespace placement is upstream-facing: this is a pure companion to interval integrals.








open intervalIntegral in

theorem intervalIntegral.integral_mul_exp_primitive {a : ℝ → ℝ} {C T t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T)
    (ha : IntegrableOn a (Icc (0 : ℝ) T))
    (ha_nonneg : ∀ s ∈ Icc (0 : ℝ) T, 0 ≤ a s)
    (ha_le : ∀ s ∈ Icc (0 : ℝ) T, a s ≤ C) :
    (∫ s in (0 : ℝ)..t, a s * Real.exp (∫ r in (0 : ℝ)..s, a r)) =
      Real.exp (∫ r in (0 : ℝ)..t, a r) - 1 := by sorry
