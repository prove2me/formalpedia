-- Prove2me | solution 1 for Erdos146.BinaryPairKernel.childMarginal_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T05:00:28.466854+00:00
-- url     : https://prove2.me/submissions/c195fe49-08ad-4620-91cd-13add49315af

import Definitions.Def_erdos146_core2
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Theorems.Thm_Erdos146_independentBinaryPairMass_nonneg

open Erdos146
open Erdos146.BinaryPairKernel
open Filter Finset SimpleGraph
open scoped Topology

theorem solution (kernel : BinaryPairKernel) :
    0 ≤ kernel.childMarginal := by
  unfold childMarginal
  apply Finset.sum_nonneg
  intro left _
  apply Finset.sum_nonneg
  intro right _
  exact mul_nonneg
    (independentBinaryPairMass_nonneg
      kernel.parentProbability_nonneg kernel.parentProbability_le_one
      left right)
    (kernel.childProbability_nonneg left right)
