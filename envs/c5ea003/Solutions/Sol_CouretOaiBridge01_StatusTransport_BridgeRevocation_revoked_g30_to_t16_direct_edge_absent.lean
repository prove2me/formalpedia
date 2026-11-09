-- Prove2me | solution 1 for CouretOaiBridge01.StatusTransport.BridgeRevocation.revoked_g30_to_t16_direct_edge_absent
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T21:01:18.706131+00:00
-- url     : https://prove2.me/submissions/b3f9f50d-c4a5-4c3f-a155-f9341533c4e1

import Definitions.Def_Couret_STAT_TRANS_13_BridgeRevocation_01cdfed00ec1
import Mathlib.Data.Set.Basic
import Theorems.Thm_CouretOaiBridge01_StatusTransport_ConcreteRegistry_registered_edges_are_case_local
import Definitions.Def_Couret_STAT_TRANS_12_FirstBridgeInvalidation_20076e79da66

/-!
# STAT-TRANS-13 — Controlled bridge revocation

This layer separates the historical existence of a BridgeReceipt from its
current admission state.

Revoking the first G30 -> T16 justification receipt must remove the cross-case
transport while preserving:
- the receipt metadata for audit;
- the local T16 proof graph;
- all scope firewalls and axis separation.

Revocation means "do not use this receipt for current transport".  It does not
rewrite history and does not assert that either endpoint claim is false.

No RH claim. No novelty claim.
-/

namespace CouretOaiBridge01
namespace StatusTransport
namespace BridgeRevocation

open ConcreteRegistry
open RefinedPolicy
open BridgeReceipts
open FirstAdmittedBridge

















theorem first_bridge_disabled_after_revocation :
    ¬ GovernedReceiptRelation governedRegistryV1Revoked
      .justification .g30Finite .t16FixedModulus := by
  simp [GovernedReceiptRelation, governedRegistryV1Revoked, revokedFirstBridge]





/-- No direct governed cross-case justification edge remains after revocation. -/
theorem p2m_local_revoked_g30_to_t16_direct_edge_absent :
    ¬ GovernedBridgedRelation governedRegistryV1Revoked
      .justification .g30Finite .t16FixedModulus := by
  intro h
  rcases h with hlocal | hreceipt
  · rcases hlocal with ⟨edge, hedge, hsource, htarget, _⟩
    have hcase : caseOf edge.source = caseOf edge.target :=
      registered_edges_are_case_local edge hedge
    have : caseOf ConcreteNode.g30Finite =
        caseOf ConcreteNode.t16FixedModulus := by
      calc
        caseOf ConcreteNode.g30Finite = caseOf edge.source :=
          congrArg caseOf hsource.symm
        _ = caseOf edge.target := hcase
        _ = caseOf ConcreteNode.t16FixedModulus :=
          congrArg caseOf htarget
    cases this
  · exact first_bridge_disabled_after_revocation hreceipt





end BridgeRevocation
end StatusTransport
end CouretOaiBridge01

theorem solution : Not
  (CouretOaiBridge01.StatusTransport.BridgeRevocation.GovernedBridgedRelation
    CouretOaiBridge01.StatusTransport.BridgeRevocation.governedRegistryV1Revoked
    CouretOaiBridge01.StatusTransport.RefinedPolicy.StatusAxisV2.justification
    CouretOaiBridge01.StatusTransport.ConcreteRegistry.ConcreteNode.g30Finite
    CouretOaiBridge01.StatusTransport.ConcreteRegistry.ConcreteNode.t16FixedModulus) := @_root_.CouretOaiBridge01.StatusTransport.BridgeRevocation.p2m_local_revoked_g30_to_t16_direct_edge_absent

