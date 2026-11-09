-- Prove2me | Theorems.Thm_CouretOaiBridge01_StatusTransport_BridgeReceipts_proof_receipt_cannot_transport_novelty
-- name    : CouretOaiBridge01.StatusTransport.BridgeReceipts.proof_receipt_cannot_transport_novelty
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T21:00:55.970754+00:00
-- url     : https://prove2.me/theorems/75c9bcf6-193b-4a72-88d7-ae2d57b08efd
-- title:
--   A proof-kind receipt cannot claim the novelty axis
-- statement:
--   A bridge receipt records source and target nodes, one of semantic/replay/novelty/justification axes, a dependency kind, nonempty bridge-statement/witness/version strings, reopened axes including its own axis, different source/target cases, and a true refined-policy permission. If a receipt has dependency kind proof, then its axis is not novelty.
--
--   The refined policy requires a novelty-kind dependency for novelty transport.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/d71ed2dafa9daa082f1a801b51d8a58abdb2c473/research/lean/CouretOaiBridge01/STAT_TRANS_08_BridgeReceipts.lean#L133-L143, lines 133–143; source file SHA-256 a2817030ed438a98e6bcab5eb9b3ab12126da52b32e8fe7707b8fcf1cc99482e; theorem CouretOaiBridge01.StatusTransport.BridgeReceipts.proof_receipt_cannot_transport_novelty

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

theorem proof_receipt_cannot_transport_novelty
    (r : BridgeReceipt)
    (hk : r.kind = DependencyKind.proof) :
    r.axis ≠ StatusAxisV2.novelty := by sorry


end BridgeReceipts
end StatusTransport
end CouretOaiBridge01
