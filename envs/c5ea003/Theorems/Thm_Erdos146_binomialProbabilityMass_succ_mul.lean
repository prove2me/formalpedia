-- Prove2me | Theorems.Thm_Erdos146_binomialProbabilityMass_succ_mul
-- name    : Erdos146.binomialProbabilityMass_succ_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T04:42:13.951217+00:00
-- url     : https://prove2.me/theorems/a4cf9706-f8fe-4a34-b30f-cb89f384e151
-- title:
--   Binomial mass recursion
-- statement:
--   The one-step recursion for the binomial probability mass function, used to sum the weight distribution of Boolean words against the Hamming-ball radius.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L10781-L10802

import Definitions.Def_erdos146_core2
import Mathlib.Analysis.RCLike.Basic

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem Erdos146.binomialProbabilityMass_succ_mul
    (trialCount successCount : ℕ) (probability : ℝ)
    (hcount : successCount < trialCount) :
    binomialProbabilityMass trialCount (successCount + 1) probability *
        ((successCount + 1 : ℕ) : ℝ) * (1 - probability) =
      binomialProbabilityMass trialCount successCount probability *
        ((trialCount - successCount : ℕ) : ℝ) * probability := by sorry
