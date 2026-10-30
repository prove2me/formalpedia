-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch9_LimitLaws_CompositionParts
-- name    : AnalyticCombinatorics_Ch9_LimitLaws_CompositionParts
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-28T15:51:27.041104+00:00
-- url     : https://prove2.me/theorems/0affca69-d52a-424e-bd8a-ea6e96f0f513
-- title:
--   A Gaussian limit for the composition-gap part-count model
-- statement:
--   The mathematical objects and operations are specified by the following source definitions.
--
--   ```lean
--   def compositionGapP (n : ℕ) : Measure (CompositionGapΩ n) :=
--     P (n - 1)
--   ```
--
--   ```lean
--   def compositionBeta (n : ℕ) : ℝ :=
--     ((n - 1 : ℕ) : ℝ)
--   ```
--
--   ```lean
--   def compositionSignSum (n : ℕ) (ω : CompositionGapΩ n) : ℝ :=
--     S (n - 1) ω
--   ```
--
--   ```lean
--   def compositionParts (n : ℕ) (ω : CompositionGapΩ n) : ℝ :=
--     1 + compositionGapCount n ω
--   ```
--
--   ```lean
--   abbrev CompositionGapΩ (n : ℕ) := Ω (n - 1)
--   ```
--
--   ```lean
--   def compositionGapCount (n : ℕ) (ω : CompositionGapΩ n) : ℝ :=
--     X (n - 1) ω
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch9/LimitLaws/CompositionParts.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch9_LimitLaws_BinaryWordCLT
import Mathlib
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Number of parts in a random composition

For `n ≥ 1`, a composition of `n` with `k` parts is equivalently a choice of
`k - 1` of the `n - 1` interior gaps.  Thus the part count has the same law as
`1 + Binomial(n - 1, 1 / 2)`.

The central limit theorem is proved by reusing the local quasi-powers
instantiation for binary words from `BinaryWordCLT.lean`, shifted from `n` to
`n - 1` and then translated by the deterministic `+1`.
-/

noncomputable section

open Complex Filter MeasureTheory ProbabilityTheory

open scoped Topology

namespace AnalyticCombinatorics
namespace Ch9
namespace LimitLaws

/-- Binary gap space for a composition of `n`, with `n - 1` interior gaps. -/
abbrev CompositionGapΩ (n : ℕ) := Ω (n - 1)

/-- Product measure for independent fair choices of the `n - 1` gaps. -/
def compositionGapP (n : ℕ) : Measure (CompositionGapΩ n) :=
  P (n - 1)

instance compositionGapP_isProbabilityMeasure (n : ℕ) :
    IsProbabilityMeasure (compositionGapP n) := by
  unfold compositionGapP
  infer_instance

/-- Number of selected gaps in the sign-coded model. -/
def compositionGapCount (n : ℕ) (ω : CompositionGapΩ n) : ℝ :=
  X (n - 1) ω

/-- Number of parts: one plus the number of selected interior gaps. -/
def compositionParts (n : ℕ) (ω : CompositionGapΩ n) : ℝ :=
  1 + compositionGapCount n ω

end LimitLaws
end Ch9
end AnalyticCombinatorics


