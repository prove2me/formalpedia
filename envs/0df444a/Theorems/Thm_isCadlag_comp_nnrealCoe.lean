-- Prove2me | Theorems.Thm_isCadlag_comp_nnrealCoe
-- name    : isCadlag_comp_nnrealCoe
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T22:08:43.09499+00:00
-- url     : https://prove2.me/theorems/9c0e77b1-dee8-4193-8f5c-f24d7ed8c6f6
-- title:
--   LeanLevy: isCadlag_comp_nnrealCoe
-- statement:
--   Restricting a real-indexed càdlàg path to nonnegative real time preserves its càdlàg property. Pinned source theorem, with its original proof previously compiled; awaiting remote Prove2Me verification.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Processes/Cadlag.lean#L286

import Definitions.Def_LeanLevy_Processes_Cadlag
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Order.Preorder.Finite
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.Algebra.Monoid

universe u_3
theorem isCadlag_comp_nnrealCoe : ∀ {β : Type u_3} [inst : TopologicalSpace β] {f : Real → β},
  @ProbabilityTheory.IsCadlag Real β
      (@UniformSpace.toTopologicalSpace Real (@PseudoMetricSpace.toUniformSpace Real Real.pseudoMetricSpace)) inst
      Real.instPreorder f →
    @ProbabilityTheory.IsCadlag NNReal β NNReal.instTopologicalSpace inst
      (@PartialOrder.toPreorder NNReal NNReal.instPartialOrder) fun t => f ↑t := by sorry
