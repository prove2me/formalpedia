-- Prove2me | solution 1 for CouretOaiBridge01.StatusTransport.BridgeReceiptMutationSuite.B16_current_registry_still_case_local
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T21:00:54.112516+00:00
-- url     : https://prove2.me/submissions/0046de5c-c43a-442a-b740-3eac7d2903d4

import Definitions.Def_Couret_STAT_TRANS_10_BridgeReceiptMutationSuite_2f6736ccd928
import Mathlib.Data.Set.Basic
import Theorems.Thm_CouretOaiBridge01_StatusTransport_BridgeReceipts_current_direct_relations_are_case_local
import Definitions.Def_Couret_STAT_TRANS_08_BridgeReceipts_087a93e69025

/-!
# STAT-TRANS-10 — Bridge receipt mutation suite

This layer pre-specifies structural ACCEPT / REJECT tests for bridge drafts
before any real cross-case bridge is admitted to `currentBridgeReceipts`.

A structurally accepted draft is not a scientifically admitted bridge.
Admission still requires construction of a `BridgeReceipt` and explicit
registration.

No RH claim. No novelty claim.
-/

namespace CouretOaiBridge01
namespace StatusTransport
namespace BridgeReceiptMutationSuite

open ConcreteRegistry
open RefinedPolicy
open BridgeReceipts





























/-! ## Pre-specified ACCEPT / REJECT matrix -/

























/-!
A concrete synthetic receipt demonstrates the distinction between
"structurally admissible" and "currently registered".  It is never inserted
into `currentBridgeReceipts`.
-/









/--
The current production registry remains cross-case empty even though the
mutation suite contains a synthetic receipt value.
-/
theorem p2m_local_B16_current_registry_still_case_local
    {axis : StatusAxisV2} {a b : ConcreteNode}
    (h : BridgedRelation currentBridgeReceipts axis a b) :
    caseOf a = caseOf b :=
  current_direct_relations_are_case_local h

end BridgeReceiptMutationSuite
end StatusTransport
end CouretOaiBridge01

theorem solution : ∀ {axis : CouretOaiBridge01.StatusTransport.RefinedPolicy.StatusAxisV2}
  {a b : CouretOaiBridge01.StatusTransport.ConcreteRegistry.ConcreteNode},
  CouretOaiBridge01.StatusTransport.BridgeReceipts.BridgedRelation
      CouretOaiBridge01.StatusTransport.BridgeReceipts.currentBridgeReceipts axis a b →
    @Eq.{1} CouretOaiBridge01.StatusTransport.ConcreteRegistry.ScientificCase
      (CouretOaiBridge01.StatusTransport.ConcreteRegistry.caseOf a)
      (CouretOaiBridge01.StatusTransport.ConcreteRegistry.caseOf b) := @_root_.CouretOaiBridge01.StatusTransport.BridgeReceiptMutationSuite.p2m_local_B16_current_registry_still_case_local

