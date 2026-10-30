-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch9_LimitLaws_BinaryWordCLT
-- name    : AnalyticCombinatorics_Ch9_LimitLaws_BinaryWordCLT
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-28T15:44:37.674993+00:00
-- url     : https://prove2.me/theorems/e6bb1344-1b2e-4510-9eb4-9697f29fe532
-- title:
--   Binary Word C L T
-- statement:
--   The mathematical objects and operations are specified by the following source definitions.
--
--   ```lean
--   abbrev Ω (n : ℕ) := Fin n → ℝ
--   ```
--
--   ```lean
--   def P (n : ℕ) : Measure (Ω n) :=
--     Measure.pi (fun _ : Fin n => oneBitSignLaw)
--   ```
--
--   ```lean
--   def S (n : ℕ) (ω : Ω n) : ℝ :=
--     ∑ i, ω i
--   ```
--
--   ```lean
--   def X (n : ℕ) (ω : Ω n) : ℝ :=
--     (S n ω + n) / 2
--   ```
--
--   ```lean
--   def oneBitSignLaw : Measure ℝ :=
--     ENNReal.ofReal (1 / 2 : ℝ) • (Measure.dirac (-1 : ℝ) + Measure.dirac (1 : ℝ))
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch9/LimitLaws/BinaryWordCLT.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Mathlib
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Binary word counts and the local quasi-powers interface

The one-bit uniform binary-word count has characteristic function zero at `π`.
Consequently it cannot satisfy a global exponential-form `hChar` assumption, whose
right hand side is a complex exponential and therefore never zero.

The binary-word central limit theorem below uses the faithful local interface from
`QuasiPowers.lean`.  We encode bits as signs `-1, 1`; the number of ones in a word is
`(sum of signs + n) / 2`, so the usual count normalization is pointwise equal to the
standardized sign sum.
-/

noncomputable section

open Complex Filter MeasureTheory ProbabilityTheory

open scoped Topology

namespace AnalyticCombinatorics
namespace Ch9
namespace LimitLaws

/-- The one-bit sign law, using `-1` for zero and `1` for one. -/
def oneBitSignLaw : Measure ℝ :=
  ENNReal.ofReal (1 / 2 : ℝ) • (Measure.dirac (-1 : ℝ) + Measure.dirac (1 : ℝ))

instance oneBitSignLaw_isProbabilityMeasure : IsProbabilityMeasure oneBitSignLaw := by
  rw [oneBitSignLaw]
  constructor
  simp [ENNReal.inv_two_add_inv_two]

/-- Binary words of length `n`, sign-coded as coordinates in `{-1, 1}`. -/
abbrev Ω (n : ℕ) := Fin n → ℝ

/-- Product measure for a uniform sign-coded binary word. -/
def P (n : ℕ) : Measure (Ω n) :=
  Measure.pi (fun _ : Fin n => oneBitSignLaw)

instance P_isProbabilityMeasure (n : ℕ) : IsProbabilityMeasure (P n) := by
  unfold P
  infer_instance

/-- Sum of signs in a sign-coded binary word. -/
def S (n : ℕ) (ω : Ω n) : ℝ :=
  ∑ i, ω i

/-- Number of ones in a sign-coded binary word. -/
def X (n : ℕ) (ω : Ω n) : ℝ :=
  (S n ω + n) / 2

end LimitLaws
end Ch9
end AnalyticCombinatorics


