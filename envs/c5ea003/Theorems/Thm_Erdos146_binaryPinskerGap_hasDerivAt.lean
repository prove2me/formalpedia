-- Prove2me | Theorems.Thm_Erdos146_binaryPinskerGap_hasDerivAt
-- name    : Erdos146.binaryPinskerGap_hasDerivAt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T04:39:53.508578+00:00
-- url     : https://prove2.me/theorems/b974376a-e26c-4a74-bdb5-4353e4ff51d5
-- title:
--   Derivative of the Pinsker gap
-- statement:
--   The Pinsker-type gap between binary entropy and its quadratic lower bound is differentiable, with the stated derivative. Section 5 uses this to locate the maximum of the entropy expression (12), which is attained at $u = 0$ and equals $\kappa$.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L9546-L9558

import Definitions.Def_erdos146_core2
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Topology.Algebra.Module.ModuleTopology

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem Erdos146.binaryPinskerGap_hasDerivAt {q : ℝ}
    (hqzero : q ≠ 0) (hqone : q ≠ 1) :
    HasDerivAt binaryPinskerGap (binaryPinskerGapDeriv q) q := by sorry
