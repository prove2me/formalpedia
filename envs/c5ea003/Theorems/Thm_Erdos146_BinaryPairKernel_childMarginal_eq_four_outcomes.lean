-- Prove2me | Theorems.Thm_Erdos146_BinaryPairKernel_childMarginal_eq_four_outcomes
-- name    : Erdos146.BinaryPairKernel.childMarginal_eq_four_outcomes
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T04:40:56.348306+00:00
-- url     : https://prove2.me/theorems/86f96179-9bb6-4529-92f7-f6b6d2d4b2fc
-- title:
--   Child marginal in terms of the four parent-child outcomes
-- statement:
--   Supporting fact for the two-bit pair kernel of Section 5, which governs how much conditional entropy a child bit can carry given its two parent bits. The marginal distribution of the child bit decomposes over the four possible outcomes of a parent pair.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L10028-L10040

import Definitions.Def_erdos146_core2
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring.Basic

open Erdos146
open Erdos146.BinaryPairKernel
open Filter Finset SimpleGraph
open scoped Topology

theorem Erdos146.BinaryPairKernel.childMarginal_eq_four_outcomes (kernel : BinaryPairKernel) :
    kernel.childMarginal =
      (1 - kernel.parentProbability) ^ 2 *
          kernel.childProbability false false +
        (1 - kernel.parentProbability) * kernel.parentProbability *
          kernel.childProbability false true +
        kernel.parentProbability * (1 - kernel.parentProbability) *
          kernel.childProbability true false +
        kernel.parentProbability ^ 2 *
          kernel.childProbability true true := by sorry
