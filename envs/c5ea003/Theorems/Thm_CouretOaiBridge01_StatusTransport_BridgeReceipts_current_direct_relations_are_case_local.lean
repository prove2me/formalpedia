-- Prove2me | Theorems.Thm_CouretOaiBridge01_StatusTransport_BridgeReceipts_current_direct_relations_are_case_local
-- name    : CouretOaiBridge01.StatusTransport.BridgeReceipts.current_direct_relations_are_case_local
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:43:43.24726+00:00
-- url     : https://prove2.me/theorems/58ce999e-f002-4b5a-9599-ae775c876d0a
-- title:
--   Every currently admitted direct relation stays in one case
-- statement:
--   Fix the concrete node registry and the refined four-axis policy. For a receipt list $L$, its receipt relation on axis $a$ contains $(x,y)$ exactly when a receipt in $L$ has that axis and those endpoints. Its bridged relation is the union of this relation and the case-local base relation. For every axis $a$ and nodes $x,y$, if they are related by the bridged relation with the current empty receipt registry, then
--
--   $$\operatorname{case}(x)=\operatorname{case}(y).$$
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/d71ed2dafa9daa082f1a801b51d8a58abdb2c473/research/lean/CouretOaiBridge01/STAT_TRANS_08_BridgeReceipts.lean#L118-L131, lines 118–131; source file SHA-256 a2817030ed438a98e6bcab5eb9b3ab12126da52b32e8fe7707b8fcf1cc99482e; theorem CouretOaiBridge01.StatusTransport.BridgeReceipts.current_direct_relations_are_case_local

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

theorem current_direct_relations_are_case_local
    {axis : StatusAxisV2} {a b : ConcreteNode}
    (h : BridgedRelation currentBridgeReceipts axis a b) :
    caseOf a = caseOf b := by sorry




end BridgeReceipts
end StatusTransport
end CouretOaiBridge01
