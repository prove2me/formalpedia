-- Prove2me | Theorems.Thm_CouretOaiBridge01_StatusTransport_BridgeRevocation_revoked_g30_to_t16_direct_edge_absent
-- name    : CouretOaiBridge01.StatusTransport.BridgeRevocation.revoked_g30_to_t16_direct_edge_absent
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T21:01:16.231866+00:00
-- url     : https://prove2.me/theorems/ab62d786-8d18-4979-be88-e9f71e137aff
-- title:
--   Revocation removes the direct cross-case edge
-- statement:
--   The governed registry consists of one historical receipt for justification transport from g30Finite to t16FixedModulus. Registry V1 enables it; the revoked registry contains the same receipt with enabled=false. The governed bridged relation is the union of the case-local refined relation and enabled receipt edges. The governed bridged relation for the revoked registry has no direct justification edge g30Finite→t16FixedModulus.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/f72b0e6ff3408c36460034dc02c539a1fe7e8233/research/lean/CouretOaiBridge01/STAT_TRANS_13_BridgeRevocation.lean#L90-L108, lines 90–108; source file SHA-256 65bf158abed25be0c2894ee1660e996bc9623ab11c4ad9856096b8e7a976acc4; theorem CouretOaiBridge01.StatusTransport.BridgeRevocation.revoked_g30_to_t16_direct_edge_absent

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

theorem revoked_g30_to_t16_direct_edge_absent :
    ¬ GovernedBridgedRelation governedRegistryV1Revoked
      .justification .g30Finite .t16FixedModulus := by sorry






end BridgeRevocation
end StatusTransport
end CouretOaiBridge01
