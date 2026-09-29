-- Prove2me | solution 1 for Zeta23.LeafIntegrals.integral_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T07:44:34.008808+00:00
-- url     : https://prove2.me/submissions/6a914233-c451-4c38-a2f8-648ef0ba354e

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

-- from Zeta23.Defs.LeafIntegrals
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
Zeta23/Defs/LeafIntegrals.lean — self-contained elementary integral bounds used as drop-ins by
§5's lem:ends (Zeta23/PrimeSideA/EndsE1.lean). Imports only Mathlib.
-/

open MeasureTheory Real Set

noncomputable section

namespace Zeta23.LeafIntegrals




/-! ## (W3) core: ∫ ψ(r)² (2+|r|)² dr ≤ 18 L² + 18 (c/w)² for any even 0 ≤ ψ ≤ L with ψ(r) ≤ c/(w r²) -/


end Zeta23.LeafIntegrals
end
open MeasureTheory Real Set

theorem solution (T : ℝ) (hT : 0 < T) :
    ∫ τ in T..(2 * T), ((1 + (2 * T - τ)) ^ 2)⁻¹ ≤ 1 := by
  have hderiv : ∀ x ∈ uIcc T (2 * T),
      HasDerivAt (fun τ : ℝ => (1 + (2 * T - τ))⁻¹) (((1 + (2 * T - x)) ^ 2)⁻¹) x := by
    intro x hx
    rw [uIcc_of_le (by linarith)] at hx
    have hpos : (1 + (2 * T - x)) ≠ 0 := by linarith [hx.2]
    have h1 : HasDerivAt (fun τ : ℝ => 1 + (2 * T - τ)) (-1) x := by
      simpa using ((hasDerivAt_id x).const_sub (2 * T)).const_add 1
    have h2 := h1.inv hpos
    have heq : -(-1) / (1 + (2 * T - x)) ^ 2 = ((1 + (2 * T - x)) ^ 2)⁻¹ := by
      rw [neg_neg, one_div]
    exact heq ▸ h2
  have hcont : ContinuousOn (fun x : ℝ => ((1 + (2 * T - x)) ^ 2)⁻¹) (uIcc T (2 * T)) := by
    rw [uIcc_of_le (by linarith)]
    apply ContinuousOn.inv₀ (by fun_prop)
    intro x hx; have : 0 < 1 + (2 * T - x) := by linarith [hx.2]
    positivity
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable)]
  have h1T : 0 < 1 + T := by linarith
  rw [show 2 * T - 2 * T = (0:ℝ) by ring, show 2 * T - T = T by ring]
  simp only [add_zero, inv_one]
  have : 0 < (1 + T)⁻¹ := by positivity
  linarith
