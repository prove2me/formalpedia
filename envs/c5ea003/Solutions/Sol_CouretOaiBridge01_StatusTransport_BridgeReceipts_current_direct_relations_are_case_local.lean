-- Prove2me | solution 1 for CouretOaiBridge01.StatusTransport.BridgeReceipts.current_direct_relations_are_case_local
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:43:46.914197+00:00
-- url     : https://prove2.me/submissions/44ef18c8-8101-41f1-bfac-71f2e570dfb8

import Definitions.Def_Couret_STAT_TRANS_08_BridgeReceipts_087a93e69025
import Mathlib.Data.Set.Basic
import Theorems.Thm_CouretOaiBridge01_StatusTransport_ConcreteRegistry_registered_edges_are_case_local
import Definitions.Def_Couret_STAT_TRANS_07_ConcreteRegistry_d1fd54ec4183
import Definitions.Def_Couret_STAT_TRANS_07_RefinedPolicy_ed1e12af9529

/-!
# STAT-TRANS-08 — Bridge receipts

Cross-case transport is forbidden by default.  An exceptional bridge is
represented by an explicit receipt carrying source, target, axis, dependency
kind, bridge statement, witness reference, version reference, and declared
invalidation consequences.

Lean verifies the receipt schema and the graph admission rule.  A string
reference to an external artifact is metadata, not authentication of that
artifact.

No RH claim. No novelty claim.
-/

namespace CouretOaiBridge01
namespace StatusTransport
namespace BridgeReceipts

open ConcreteRegistry
open RefinedPolicy





















/-- With an empty receipt registry, the bridged relation reduces to the base relation. -/
theorem current_relation_eq_base
    (axis : StatusAxisV2) (a b : ConcreteNode) :
    BridgedRelation currentBridgeReceipts axis a b ↔
      V2Relation concreteEdges axis a b := by
  simp [BridgedRelation, ReceiptRelation, currentBridgeReceipts]

/-- Therefore every currently admitted direct relation remains case-local. -/
theorem p2m_local_current_direct_relations_are_case_local
    {axis : StatusAxisV2} {a b : ConcreteNode}
    (h : BridgedRelation currentBridgeReceipts axis a b) :
    caseOf a = caseOf b := by
  have hbase : V2Relation concreteEdges axis a b :=
    (current_relation_eq_base axis a b).mp h
  rcases hbase with ⟨edge, hedge, hsource, htarget, _⟩
  have hlocal : caseOf edge.source = caseOf edge.target :=
    registered_edges_are_case_local edge hedge
  calc
    caseOf a = caseOf edge.source := congrArg caseOf hsource.symm
    _ = caseOf edge.target := hlocal
    _ = caseOf b := congrArg caseOf htarget



end BridgeReceipts
end StatusTransport
end CouretOaiBridge01

theorem solution : ∀ {axis : CouretOaiBridge01.StatusTransport.RefinedPolicy.StatusAxisV2}
  {a b : CouretOaiBridge01.StatusTransport.ConcreteRegistry.ConcreteNode},
  CouretOaiBridge01.StatusTransport.BridgeReceipts.BridgedRelation
      CouretOaiBridge01.StatusTransport.BridgeReceipts.currentBridgeReceipts axis a b →
    @Eq.{1} CouretOaiBridge01.StatusTransport.ConcreteRegistry.ScientificCase
      (CouretOaiBridge01.StatusTransport.ConcreteRegistry.caseOf a)
      (CouretOaiBridge01.StatusTransport.ConcreteRegistry.caseOf b) := @_root_.CouretOaiBridge01.StatusTransport.BridgeReceipts.p2m_local_current_direct_relations_are_case_local

