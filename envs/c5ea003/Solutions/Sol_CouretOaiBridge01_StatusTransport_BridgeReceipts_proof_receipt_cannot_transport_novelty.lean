-- Prove2me | solution 1 for CouretOaiBridge01.StatusTransport.BridgeReceipts.proof_receipt_cannot_transport_novelty
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T21:01:02.485213+00:00
-- url     : https://prove2.me/submissions/30a26d54-823e-41b2-958e-8fda2bab2788

import Definitions.Def_Couret_STAT_TRANS_08_BridgeReceipts_087a93e69025
import Mathlib.Data.Set.Basic
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
A proof bridge cannot be declared as a novelty transport under the refined
policy; novelty requires an explicit novelty dependency.
-/
theorem p2m_local_proof_receipt_cannot_transport_novelty
    (r : BridgeReceipt)
    (hk : r.kind = DependencyKind.proof) :
    r.axis ≠ StatusAxisV2.novelty := by
  intro ha
  have hp := r.policyOk
  simp [hk, ha, permitsV2] at hp

end BridgeReceipts
end StatusTransport
end CouretOaiBridge01

theorem solution : ∀ (r : CouretOaiBridge01.StatusTransport.BridgeReceipts.BridgeReceipt),
  @Eq.{1} CouretOaiBridge01.StatusTransport.DependencyKind
      (CouretOaiBridge01.StatusTransport.BridgeReceipts.BridgeReceipt.kind r)
      CouretOaiBridge01.StatusTransport.DependencyKind.proof →
    @Ne.{1} CouretOaiBridge01.StatusTransport.RefinedPolicy.StatusAxisV2
      (CouretOaiBridge01.StatusTransport.BridgeReceipts.BridgeReceipt.axis r)
      CouretOaiBridge01.StatusTransport.RefinedPolicy.StatusAxisV2.novelty := @_root_.CouretOaiBridge01.StatusTransport.BridgeReceipts.p2m_local_proof_receipt_cannot_transport_novelty

