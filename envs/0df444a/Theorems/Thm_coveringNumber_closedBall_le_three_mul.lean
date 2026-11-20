-- Prove2me | Theorems.Thm_coveringNumber_closedBall_le_three_mul
-- name    : coveringNumber_closedBall_le_three_mul
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T07:22:47.763063+00:00
-- url     : https://prove2.me/theorems/cc099187-548f-4212-ac20-7644491b07cb
-- title:
--   coveringNumber closedBall le three mul
-- statement:
--   The source theorem `coveringNumber_closedBall_le_three_mul` is extracted from `BrownianMotion.Continuity.CoveringNumber`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_BrownianMotion_Continuity_CoveringNumber_F001

/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

/-!
# Covering and packing numbers

### References
- Vershynin, High-Dimensional Probability (section 4.2)
-/

@[expose] public section

open EMetric Set Metric
open scoped ENNReal NNReal

section PseudoEMetricSpace

variable {E : Type*} [PseudoEMetricSpace E] {r ε ε' : ℝ≥0} {A B C : Set E}

end PseudoEMetricSpace

section Volume

open MeasureTheory

section PseudoEMetricSpace
variable {X : Type*} [PseudoEMetricSpace X] {ε : ℝ≥0} {s N : Set X}

end PseudoEMetricSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {ε : ℝ≥0} {A : Set E} {C : Set E}

theorem coveringNumber_closedBall_le_three_mul [Nontrivial E]
    {x : E} {r : ℝ≥0} (hr_zero : r ≠ 0) (hε : ε ≤ r) :
    (coveringNumber ε (Metric.closedEBall x r) : ℝ≥0∞)
      ≤ (3 * r / (ε : ℝ≥0∞)) ^ (Module.finrank ℝ E) := by sorry
