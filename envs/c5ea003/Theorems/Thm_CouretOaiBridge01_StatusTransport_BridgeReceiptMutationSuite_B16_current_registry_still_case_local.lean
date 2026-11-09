-- Prove2me | Theorems.Thm_CouretOaiBridge01_StatusTransport_BridgeReceiptMutationSuite_B16_current_registry_still_case_local
-- name    : CouretOaiBridge01.StatusTransport.BridgeReceiptMutationSuite.B16_current_registry_still_case_local
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T21:00:48.002199+00:00
-- url     : https://prove2.me/theorems/08acc00e-d611-4af2-93d8-5d3e727f1944
-- title:
--   Synthetic mutation tests leave current direct relations case-local
-- statement:
--   For every refined status axis and concrete nodes $x,y$, if the current bridged relation relates them on that axis, then their scientific cases are equal.
--
--   The conclusion is independent of the presence of synthetic receipt values elsewhere in the source.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/d71ed2dafa9daa082f1a801b51d8a58abdb2c473/research/lean/CouretOaiBridge01/STAT_TRANS_10_BridgeReceiptMutationSuite.lean#L204-L212, lines 204–212; source file SHA-256 577a41a0270bef14eb9b020e54ed3421c0cf6bb66d2fe6526f3706c1b87392ba; theorem CouretOaiBridge01.StatusTransport.BridgeReceiptMutationSuite.B16_current_registry_still_case_local

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

theorem B16_current_registry_still_case_local
    {axis : StatusAxisV2} {a b : ConcreteNode}
    (h : BridgedRelation currentBridgeReceipts axis a b) :
    caseOf a = caseOf b := by sorry


end BridgeReceiptMutationSuite
end StatusTransport
end CouretOaiBridge01
