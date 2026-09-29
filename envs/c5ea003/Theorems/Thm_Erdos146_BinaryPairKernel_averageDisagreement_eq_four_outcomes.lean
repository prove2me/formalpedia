-- Prove2me | Theorems.Thm_Erdos146_BinaryPairKernel_averageDisagreement_eq_four_outcomes
-- name    : Erdos146.BinaryPairKernel.averageDisagreement_eq_four_outcomes
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T04:41:10.167048+00:00
-- url     : https://prove2.me/theorems/1510e54e-e8f2-4778-ac0f-87711518e96d
-- title:
--   Average disagreement in terms of the four parent-child outcomes
-- statement:
--   Supporting fact for the two-bit pair kernel of Section 5, which governs how much conditional entropy a child bit can carry given its two parent bits. The kernel's average disagreement decomposes over the four possible outcomes of a parent pair, which is the form used when the entropy functional is evaluated coordinatewise.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L10065-L10075

import Definitions.Def_erdos146_core2
import Mathlib.Analysis.RCLike.Basic

open Erdos146
open Erdos146.BinaryPairKernel
open Filter Finset SimpleGraph
open scoped Topology

theorem Erdos146.BinaryPairKernel.averageDisagreement_eq_four_outcomes (kernel : BinaryPairKernel) :
    kernel.averageDisagreement =
      (1 - kernel.parentProbability) ^ 2 *
          kernel.childProbability false false +
        kernel.parentProbability * (1 - kernel.parentProbability) +
        kernel.parentProbability ^ 2 *
          (1 - kernel.childProbability true true) := by sorry
