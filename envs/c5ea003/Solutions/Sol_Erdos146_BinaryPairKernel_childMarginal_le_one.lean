-- Prove2me | solution 1 for Erdos146.BinaryPairKernel.childMarginal_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T05:01:10.07427+00:00
-- url     : https://prove2.me/submissions/d5557776-3d7c-489f-9ea3-26fae84c500a

import Definitions.Def_erdos146_core2
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring.Basic
import Theorems.Thm_Erdos146_independentBinaryPairMass_nonneg

namespace Erdos146

section
open Filter Finset SimpleGraph
open scoped Topology

theorem independentBinaryPairMass_sum (q : ℝ) :
    (∑ left : Bool, ∑ right : Bool,
      independentBinaryPairMass q left right) = 1 := by
  simp [Fintype.univ_bool, independentBinaryPairMass, binaryCoinMass]
  ring

end

end Erdos146

open Erdos146
open Erdos146.BinaryPairKernel
open Filter Finset SimpleGraph
open scoped Topology

theorem solution (kernel : BinaryPairKernel) :
    kernel.childMarginal ≤ 1 := by
  unfold childMarginal
  calc
    (∑ left : Bool, ∑ right : Bool,
        independentBinaryPairMass kernel.parentProbability left right *
          kernel.childProbability left right) ≤
      ∑ left : Bool, ∑ right : Bool,
        independentBinaryPairMass kernel.parentProbability left right * 1 := by
          apply Finset.sum_le_sum
          intro left _
          apply Finset.sum_le_sum
          intro right _
          exact mul_le_mul_of_nonneg_left
            (kernel.childProbability_le_one left right)
            (independentBinaryPairMass_nonneg
              kernel.parentProbability_nonneg kernel.parentProbability_le_one
              left right)
    _ = 1 := by
      simpa using independentBinaryPairMass_sum kernel.parentProbability
