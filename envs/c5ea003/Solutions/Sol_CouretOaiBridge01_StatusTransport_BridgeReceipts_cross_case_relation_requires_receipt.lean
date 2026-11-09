-- Prove2me | solution 1 for CouretOaiBridge01.StatusTransport.BridgeReceipts.cross_case_relation_requires_receipt
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T21:01:18.512519+00:00
-- url     : https://prove2.me/submissions/d440b412-74cf-4217-987b-570712dadd85

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















/--
Core gate: if a relation step crosses scientific cases, it must come from an
explicit bridge receipt.  The case-local base graph cannot create it.
-/
theorem p2m_local_cross_case_relation_requires_receipt
    {receipts : List BridgeReceipt}
    {axis : StatusAxisV2}
    {a b : ConcreteNode}
    (h : BridgedRelation receipts axis a b)
    (hcase : caseOf a ≠ caseOf b) :
    ReceiptRelation receipts axis a b := by
  rcases h with hbase | hreceipt
  · rcases hbase with ⟨edge, hedge, hsource, htarget, _⟩
    have hlocal : caseOf edge.source = caseOf edge.target :=
      registered_edges_are_case_local edge hedge
    have hab : caseOf a = caseOf b := by
      calc
        caseOf a = caseOf edge.source := congrArg caseOf hsource.symm
        _ = caseOf edge.target := hlocal
        _ = caseOf b := congrArg caseOf htarget
    exact False.elim (hcase hab)
  · exact hreceipt











end BridgeReceipts
end StatusTransport
end CouretOaiBridge01

theorem solution : ∀ {receipts : List.{0} CouretOaiBridge01.StatusTransport.BridgeReceipts.BridgeReceipt}
  {axis : CouretOaiBridge01.StatusTransport.RefinedPolicy.StatusAxisV2}
  {a b : CouretOaiBridge01.StatusTransport.ConcreteRegistry.ConcreteNode},
  CouretOaiBridge01.StatusTransport.BridgeReceipts.BridgedRelation receipts axis a b →
    @Ne.{1} CouretOaiBridge01.StatusTransport.ConcreteRegistry.ScientificCase
        (CouretOaiBridge01.StatusTransport.ConcreteRegistry.caseOf a)
        (CouretOaiBridge01.StatusTransport.ConcreteRegistry.caseOf b) →
      CouretOaiBridge01.StatusTransport.BridgeReceipts.ReceiptRelation receipts axis a b := @_root_.CouretOaiBridge01.StatusTransport.BridgeReceipts.p2m_local_cross_case_relation_requires_receipt

