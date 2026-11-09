-- Prove2me | Theorems.Thm_CouretOaiBridge01_StatusTransport_BridgeReceipts_cross_case_relation_requires_receipt
-- name    : CouretOaiBridge01.StatusTransport.BridgeReceipts.cross_case_relation_requires_receipt
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T21:01:12.023827+00:00
-- url     : https://prove2.me/theorems/48b863ba-358b-42a4-a4b1-8e252525f311
-- title:
--   Every cross-case direct relation needs an explicit receipt
-- statement:
--   Fix the concrete node registry and the refined four-axis policy. For a receipt list $L$, its receipt relation on axis $a$ contains $(x,y)$ exactly when a receipt in $L$ has that axis and those endpoints. Its bridged relation is the union of this relation and the case-local base relation. For arbitrary $L,a,x,y$,
--
--   $$\operatorname{Bridged}_L(a,x,y)\land\operatorname{case}(x)\ne\operatorname{case}(y)\Longrightarrow\operatorname{Receipt}_L(a,x,y).$$
--
--   This concerns one relation step, not a transitive reachability claim.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/d71ed2dafa9daa082f1a801b51d8a58abdb2c473/research/lean/CouretOaiBridge01/STAT_TRANS_08_BridgeReceipts.lean#L75-L96, lines 75–96; source file SHA-256 a2817030ed438a98e6bcab5eb9b3ab12126da52b32e8fe7707b8fcf1cc99482e; theorem CouretOaiBridge01.StatusTransport.BridgeReceipts.cross_case_relation_requires_receipt

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

theorem cross_case_relation_requires_receipt
    {receipts : List BridgeReceipt}
    {axis : StatusAxisV2}
    {a b : ConcreteNode}
    (h : BridgedRelation receipts axis a b)
    (hcase : caseOf a ≠ caseOf b) :
    ReceiptRelation receipts axis a b := by sorry












end BridgeReceipts
end StatusTransport
end CouretOaiBridge01
