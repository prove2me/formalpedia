-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch9_LimitLaws_PermutationCycles
-- name    : AnalyticCombinatorics_Ch9_LimitLaws_PermutationCycles
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-28T15:47:14.532071+00:00
-- url     : https://prove2.me/theorems/032e00de-bb7c-4f41-9689-41aea063b78a
-- title:
--   Permutation Cycles
-- statement:
--   The mathematical objects and operations are specified by the following source definitions.
--
--   ```lean
--   def cycleH (n : ℕ) : ℝ :=
--     (harmonic n : ℝ)
--   ```
--
--   ```lean
--   def cycleP (n : ℕ) : Measure (CycleΩ n) :=
--     Measure.pi (fun i : Fin n => cycleBernoulliLaw i.1)
--   ```
--
--   ```lean
--   def cycleCount (n : ℕ) (ω : CycleΩ n) : ℝ :=
--     ∑ i, ω i
--   ```
--
--   ```lean
--   def cycleBernoulliLaw (k : ℕ) : Measure ℝ :=
--     ENNReal.ofReal (1 - ((k : ℝ) + 1)⁻¹) • Measure.dirac (0 : ℝ) +
--       ENNReal.ofReal (((k : ℝ) + 1)⁻¹) • Measure.dirac (1 : ℝ)
--   ```
--
--   ```lean
--   abbrev CycleΩ (n : ℕ) := Fin n → ℝ
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch9/LimitLaws/PermutationCycles.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Mathlib
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Cycles in a random permutation

This file instantiates the local quasi-powers interface for the Feller coupling
model of the number of cycles in a uniform random permutation:
`C_n = sum_{k=1}^n B_k`, with independent Bernoulli variables
`P(B_k = 1) = 1 / k`.
-/

noncomputable section

open Complex Filter MeasureTheory ProbabilityTheory

open scoped Topology

namespace AnalyticCombinatorics
namespace Ch9
namespace LimitLaws

/-- The harmonic scale `H_n = sum_{k=1}^n 1/k`, as a real number. -/
def cycleH (n : ℕ) : ℝ :=
  (harmonic n : ℝ)

end LimitLaws
end Ch9
end AnalyticCombinatorics


