-- Prove2me | solution 1 for Erdos146.BinaryPairKernel.childMarginal_eq_four_outcomes
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T05:01:51.704273+00:00
-- url     : https://prove2.me/submissions/53c4d552-6b5b-4bed-8eb0-a358852dbc92

import Definitions.Def_erdos146_core2
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring.Basic

open Erdos146
open Erdos146.BinaryPairKernel
open Filter Finset SimpleGraph
open scoped Topology

theorem solution (kernel : BinaryPairKernel) :
    kernel.childMarginal =
      (1 - kernel.parentProbability) ^ 2 *
          kernel.childProbability false false +
        (1 - kernel.parentProbability) * kernel.parentProbability *
          kernel.childProbability false true +
        kernel.parentProbability * (1 - kernel.parentProbability) *
          kernel.childProbability true false +
        kernel.parentProbability ^ 2 *
          kernel.childProbability true true := by
  simp [childMarginal, Fintype.univ_bool,
    independentBinaryPairMass, binaryCoinMass]
  ring
